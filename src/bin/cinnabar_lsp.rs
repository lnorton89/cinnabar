//! The `cinnabar-lsp` binary: a language server over the attached facts.
//!
//! A thin JSON-RPC shell around `cinnabar::analysis`. Every request re-runs
//! the real front-end pipeline over the open buffers, through the module
//! loader's overlay, and answers from the attachments that pipeline
//! computed. Document sync is full-text.
//!
//! The bookkeeping that is genuinely this file's own: mapping each open
//! module back to its analysis root, owning the published URI set per root
//! so a file that stops having diagnostics gets them cleared, debouncing
//! checks off the protocol loop, and rejecting stale generations before
//! publication so a slow analysis cannot overwrite a newer one. The borrow
//! checker's explanatory notes ride along as `relatedInformation` and code
//! lenses.
//!
//! Protocol payloads are built as raw JSON values: the server speaks the
//! small, stable subset of the protocol it implements.
//!
//! **Invariants:**
//! - There is no second implementation of name resolution, type inference,
//!   or borrow checking anywhere in this file. Every language-aware
//!   decision belongs to the analysis layer.
//! - A published diagnostic set is either current or not published. Stale
//!   generations are dropped rather than sent, because an editor showing
//!   errors from a previous keystroke is worse than one showing none.

use cinnabar::analysis::{
    analyze, code_actions, completions, definition, document_symbols, file_id_of, file_text_of,
    folding_ranges, hover, inlay_hints, offset_to_position, position_to_offset, prepare_rename,
    references, rename_edits, semantic_tokens, signature_help, workspace_symbols, Analysis,
    SymbolInfo, COMPLETE_FIELD, COMPLETE_KEYWORD, COMPLETE_LOCAL, SEMANTIC_TOKEN_TYPES,
};
use cinnabar::ast::{
    note_kind_name, NO_FILE, SYM_CONST, SYM_ENUM, SYM_FUN, SYM_IMPL_METHOD, SYM_MODULE,
    SYM_NATIVE_FUN, SYM_STRUCT, SYM_TRAIT, SYM_TRAIT_METHOD, SYM_TYPE, SYM_VARIANT,
};
use cinnabar::format::format_source;
use cinnabar::project;
use lsp_server::{Connection, Message, Notification, Request, RequestId, Response};
use serde_json::{json, Value};
use std::sync::mpsc::{channel, Receiver, Sender};
use std::time::{Duration, Instant};

const DIAGNOSTIC_DEBOUNCE_MS: u64 = 75;

struct AnalysisResult {
    path: String,
    generation: i64,
    analysis: Analysis,
}

struct ServerState {
    // Open documents as (file-system path, buffer text): the module
    // loader's overlay, so unsaved edits are analyzed like saved files.
    docs: Vec<(String, String)>,
    // URIs we last published diagnostics for, so stale ones are cleared.
    published: Vec<(String, Vec<String>)>,
    // Analysis roots and the root that owns each open document.  Secondary
    // modules stay in their entry file's graph when editors open them.
    roots: Vec<String>,
    doc_entries: Vec<(String, String)>,
    // Per-document edit generations and pending debounce deadlines.  A
    // completed analysis is published only when its generation is still
    // current, which makes superseded full checks harmless.
    generations: Vec<(String, i64)>,
    pending: Vec<(String, i64, Instant)>,
    // At most one full front-end run is active.  Newer generations remain
    // pending until it finishes, so sustained editing cannot accumulate
    // detached compiler threads.
    running_path: Option<String>,
    analysis_tx: Sender<AnalysisResult>,
    analysis_rx: Receiver<AnalysisResult>,
    // The one authoritative attached-fact snapshot for each root's current
    // generation. Positional requests consume this analysis; they never
    // invoke the compiler themselves.
    completed: Vec<AnalysisResult>,
    // Source-less (`NO_FILE`) diagnostic messages last surfaced per root,
    // so a `window/showMessage` fires when a message appears rather than on
    // every republish of the same analysis.
    source_less: Vec<(String, Vec<String>)>,
}

// A fatal transport failure surfaces through main's Result: there is no
// usable channel left to log through when the JSON-RPC connection itself is
// gone.
fn main() -> Result<(), String> {
    let (connection, io_threads) = Connection::stdio();
    // Built from the same array `semantic_tokens`' indices are defined
    // against, rather than a second copy of the type names here: the legend
    // and the encoder can never drift out of sync.
    let token_types: Vec<Value> = SEMANTIC_TOKEN_TYPES.iter().map(|name| json!(*name)).collect();
    let capabilities = json!({
        "textDocumentSync": 1,
        "hoverProvider": true,
        "definitionProvider": true,
        "referencesProvider": true,
        "completionProvider": { "triggerCharacters": ["."] },
        "signatureHelpProvider": { "triggerCharacters": ["(", ","] },
        "codeLensProvider": { "resolveProvider": false },
        "documentFormattingProvider": true,
        "foldingRangeProvider": true,
        "documentSymbolProvider": true,
        "workspaceSymbolProvider": true,
        "renameProvider": { "prepareProvider": true },
        "semanticTokensProvider": {
            "legend": { "tokenTypes": token_types, "tokenModifiers": [] },
            "full": true
        },
        "inlayHintProvider": true,
        "codeActionProvider": true
    });
    // lsp-server wraps this value in the InitializeResult's `capabilities`
    // field itself.
    let init_params = connection
        .initialize(capabilities)
        .map_err(|err| format!("initialize failed: {}", err))?;
    let client = init_params
        .get("clientInfo")
        .and_then(|info| info.get("name"))
        .and_then(|name| name.as_str())
        .map(|name| name.to_string())
        .unwrap_or_else(|| "unnamed client".to_string());
    log_message(&connection, &format!("cinnabar-lsp ready for {}", client))?;
    let (analysis_tx, analysis_rx) = channel();
    let mut state = ServerState {
        docs: Vec::new(),
        published: Vec::new(),
        roots: Vec::new(),
        doc_entries: Vec::new(),
        generations: Vec::new(),
        pending: Vec::new(),
        running_path: None,
        analysis_tx,
        analysis_rx,
        completed: Vec::new(),
        source_less: Vec::new(),
    };
    main_loop(&connection, &mut state)?;
    // The transport threads terminate when every channel endpoint is gone.
    // Release the server-side endpoints before waiting for those threads;
    // otherwise a clean shutdown deadlocks with the writer waiting on the
    // still-live sender held by `connection`.
    drop(connection);
    io_threads.join().map_err(|err| format!("io threads: {}", err))?;
    Ok(())
}

// Server-side logging goes through the protocol (`window/logMessage`, type
// 3 = Info), never through the process's own stdio, which the JSON-RPC
// transport owns.
fn log_message(connection: &Connection, message: &str) -> Result<(), String> {
    let note = Notification {
        method: "window/logMessage".to_string(),
        params: json!({ "type": 3, "message": message }),
    };
    connection
        .sender
        .send(Message::Notification(note))
        .map_err(|err| format!("send log message: {}", err))
}

// User-visible errors go through `window/showMessage` (type 1 = Error): the
// same notification channel as `log_message`, but shown rather than filed.
fn show_message(connection: &Connection, message: &str) -> Result<(), String> {
    let note = Notification {
        method: "window/showMessage".to_string(),
        params: json!({ "type": 1, "message": message }),
    };
    connection
        .sender
        .send(Message::Notification(note))
        .map_err(|err| format!("send show message: {}", err))
}

fn main_loop(connection: &Connection, state: &mut ServerState) -> Result<(), String> {
    loop {
        publish_completed(connection, state)?;
        start_due_analyses(state);
        let received = connection.receiver.recv_timeout(Duration::from_millis(25));
        match received {
            Ok(msg) => match msg {
            Message::Request(req) => {
                match connection.handle_shutdown(&req) {
                    Ok(true) => return Ok(()),
                    Ok(false) => dispatch_request(connection, state, req)?,
                    Err(err) => return Err(format!("shutdown handling: {}", err)),
                }
            }
            Message::Notification(note) => handle_notification(connection, state, note)?,
            Message::Response(resp) => {
                log_message(
                    connection,
                    &format!("cinnabar-lsp: ignoring unexpected response to request {:?}", resp.id),
                )?;
            }
            },
            Err(err) => {
                if !err.is_timeout() {
                    return Ok(());
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Requests
// ---------------------------------------------------------------------------

fn dispatch_request(connection: &Connection, state: &ServerState, req: Request) -> Result<(), String> {
    let method = req.method.clone();
    if method == "textDocument/hover" {
        let result = on_hover(state, &req.params);
        return send_ok(connection, req.id, result);
    }
    if method == "textDocument/definition" {
        let result = on_definition(state, &req.params);
        return send_ok(connection, req.id, result);
    }
    if method == "textDocument/references" {
        let result = on_references(state, &req.params);
        return send_ok(connection, req.id, result);
    }
    if method == "textDocument/completion" {
        let result = on_completion(state, &req.params);
        return send_ok(connection, req.id, result);
    }
    if method == "textDocument/signatureHelp" {
        let result = on_signature_help(state, &req.params);
        return send_ok(connection, req.id, result);
    }
    if method == "textDocument/codeLens" {
        let result = on_code_lens(state, &req.params);
        return send_ok(connection, req.id, result);
    }
    if method == "textDocument/formatting" {
        let result = on_formatting(state, &req.params);
        return send_ok(connection, req.id, result);
    }
    if method == "textDocument/foldingRange" {
        let result = on_folding_range(state, &req.params);
        return send_ok(connection, req.id, result);
    }
    if method == "textDocument/documentSymbol" {
        let result = on_document_symbol(state, &req.params);
        return send_ok(connection, req.id, result);
    }
    if method == "workspace/symbol" {
        let result = on_workspace_symbol(state, &req.params);
        return send_ok(connection, req.id, result);
    }
    if method == "textDocument/prepareRename" {
        let result = on_prepare_rename(state, &req.params);
        return send_ok(connection, req.id, result);
    }
    if method == "textDocument/rename" {
        let result = on_rename(state, &req.params);
        return send_ok(connection, req.id, result);
    }
    if method == "textDocument/semanticTokens/full" {
        let result = on_semantic_tokens_full(state, &req.params);
        return send_ok(connection, req.id, result);
    }
    if method == "textDocument/inlayHint" {
        let result = on_inlay_hint(state, &req.params);
        return send_ok(connection, req.id, result);
    }
    if method == "textDocument/codeAction" {
        let result = on_code_action(state, &req.params);
        return send_ok(connection, req.id, result);
    }
    let resp = Response::new_err(
        req.id,
        lsp_server::ErrorCode::MethodNotFound as i32,
        format!("method '{}' is not supported by cinnabar-lsp", method),
    );
    connection
        .sender
        .send(Message::Response(resp))
        .map_err(|err| format!("send response: {}", err))
}

fn send_ok(connection: &Connection, id: RequestId, result: Value) -> Result<(), String> {
    connection
        .sender
        .send(Message::Response(Response::new_ok(id, result)))
        .map_err(|err| format!("send response: {}", err))
}

// The (path, file id, byte offset, analysis) behind a positional request,
// or None when the params don't name a file this server can analyze.
fn positional<'state>(state: &'state ServerState, params: &Value) -> Option<(&'state Analysis, i64, i64)> {
    let uri = params.get("textDocument")?.get("uri")?.as_str()?;
    let path = uri_to_path(uri)?;
    let line = params.get("position")?.get("line")?.as_i64()?;
    let character = params.get("position")?.get("character")?.as_i64()?;
    let entry = entry_of_doc(state, &path);
    let analysis = completed_analysis(state, &entry)?;
    let file = file_id_of(analysis, &path);
    if file == NONE_ID {
        return None;
    }
    let text = file_text_of(analysis, file);
    let offset = position_to_offset(&text, line, character);
    Some((analysis, file, offset))
}

const NONE_ID: i64 = -1;

fn range_json(analysis: &Analysis, file: i64, start: i64, end: i64) -> Value {
    let text = file_text_of(analysis, file);
    let (sl, sc) = offset_to_position(&text, start);
    let (el, ec) = offset_to_position(&text, end);
    json!({
        "start": { "line": sl, "character": sc },
        "end": { "line": el, "character": ec }
    })
}

fn location_json(analysis: &Analysis, file: i64, start: i64, end: i64) -> Option<Value> {
    let path = analysis.files.get(file as usize).map(|pair| pair.0.clone())?;
    let uri = path_to_uri(&path);
    Some(json!({ "uri": uri, "range": range_json(analysis, file, start, end) }))
}

fn on_hover(state: &ServerState, params: &Value) -> Value {
    let (analysis, file, offset) = match positional(state, params) {
        Some(found) => found,
        None => return Value::Null,
    };
    match hover(analysis, file, offset) {
        Some((markdown, span)) => json!({
            "contents": { "kind": "markdown", "value": markdown },
            "range": range_json(analysis, span.0, span.1, span.2)
        }),
        None => Value::Null,
    }
}

fn on_definition(state: &ServerState, params: &Value) -> Value {
    let (analysis, file, offset) = match positional(state, params) {
        Some(found) => found,
        None => return Value::Null,
    };
    match definition(analysis, file, offset) {
        Some(span) => match location_json(analysis, span.0, span.1, span.2) {
            Some(location) => location,
            None => Value::Null,
        },
        None => Value::Null,
    }
}

fn on_references(state: &ServerState, params: &Value) -> Value {
    let (analysis, file, offset) = match positional(state, params) {
        Some(found) => found,
        None => return Value::Null,
    };
    let spans = references(analysis, file, offset);
    let mut out: Vec<Value> = Vec::new();
    let mut idx = 0usize;
    while idx < spans.len() {
        match spans.get(idx) {
            Some(span) => {
                if let Some(location) = location_json(analysis, span.0, span.1, span.2) {
                    out.push(location);
                }
            }
            None => break,
        }
        idx += 1;
    }
    Value::Array(out)
}

fn completion_kind_code(kind: i64) -> i64 {
    // LSP CompletionItemKind numbers.
    if kind == SYM_FUN || kind == SYM_NATIVE_FUN || kind == SYM_IMPL_METHOD || kind == SYM_TRAIT_METHOD {
        3 // Function
    } else if kind == SYM_STRUCT {
        22 // Struct
    } else if kind == SYM_ENUM {
        13 // Enum
    } else if kind == SYM_VARIANT {
        20 // EnumMember
    } else if kind == SYM_TRAIT {
        8 // Interface
    } else if kind == SYM_TYPE {
        7 // Class
    } else if kind == SYM_CONST {
        21 // Constant
    } else if kind == SYM_MODULE {
        9 // Module
    } else if kind == COMPLETE_LOCAL {
        6 // Variable
    } else if kind == COMPLETE_KEYWORD {
        14 // Keyword
    } else if kind == COMPLETE_FIELD {
        5 // Field
    } else {
        1 // Text
    }
}

// An identifier spliced in after a trailing dot purely so the path parses.
// It is never shown: completion filters on the text *before* the cursor, and
// the analysis it produces is discarded with the request.
const COMPLETION_STUB: &str = "cnb_completion_stub";

// True when the cursor sits after a dot that terminates an identifier path.
//
// The identifier requirement is what keeps the retry below from being paid for
// on every dot in the file: `1.`, a decimal point, or a dot typed in open space
// can never name a module, so re-analyzing for them would be a stall with no
// possible answer.
fn follows_identifier_dot(analysis: &Analysis, file: i64, offset: i64) -> bool {
    if offset <= 0 {
        return false;
    }
    let text = file_text_of(analysis, file);
    let bytes = text.as_bytes();
    match bytes.get((offset - 1) as usize) {
        Some(byte) => {
            if *byte != b'.' {
                return false;
            }
        }
        None => return false,
    }
    // Walk back over the path and require it to start where an identifier
    // could: a leading digit means a numeric literal, not a module.
    let mut start = (offset - 1) as usize;
    while start > 0 {
        let byte = match bytes.get(start - 1) {
            Some(value) => *value,
            None => break,
        };
        if byte == b'.' || byte == b'_' || byte.is_ascii_alphanumeric() {
            start -= 1;
            continue;
        }
        break;
    }
    match bytes.get(start) {
        Some(byte) => byte.is_ascii_alphabetic() || *byte == b'_',
        None => false,
    }
}

// Re-runs the front end over the open buffers with `COMPLETION_STUB` spliced
// in at the cursor, then completes at the same offset.
//
// A buffer ending in `Memory.` is a syntax error, so the parse that would have
// named the module never happens and no scope facts exist to resolve against.
// That is precisely the moment an editor asks what follows the dot.  Splicing
// an identifier in makes the path parse, which costs one extra front-end run
// on a keystroke that would otherwise answer with nothing usable.
fn completions_with_stub(state: &ServerState, path: &str, offset: i64) -> Option<Vec<(String, i64)>> {
    let mut docs = state.docs.clone();
    let doc = docs.iter_mut().find(|doc| doc.0 == path)?;
    let at = offset as usize;
    if at > doc.1.len() || !doc.1.is_char_boundary(at) {
        return None;
    }
    doc.1.insert_str(at, COMPLETION_STUB);
    let entry = entry_of_doc(state, path);
    let analysis = analyze(&entry, &docs);
    let file = file_id_of(&analysis, path);
    if file == NONE_ID {
        return None;
    }
    Some(completions(&analysis, file, offset))
}

fn on_completion(state: &ServerState, params: &Value) -> Value {
    let (analysis, file, offset) = match positional(state, params) {
        Some(found) => found,
        None => return Value::Null,
    };
    let mut items = completions(analysis, file, offset);
    // Keywords are what whole-scope completion falls back to, and none of them
    // may follow a dot; that combination means the qualified path failed to
    // resolve, so retry with a parseable buffer before answering with noise.
    // `all` holds vacuously on an empty result, which would make every dot the
    // analysis cannot answer pay for a second front-end run on each keystroke.
    // Requiring something to have been offered keeps the retry to the case it
    // was written for: a resolvable path answered with keywords.
    let keywords_only =
        !items.is_empty() && items.iter().all(|item| item.1 == COMPLETE_KEYWORD);
    if keywords_only && follows_identifier_dot(analysis, file, offset) {
        let path = params
            .get("textDocument")
            .and_then(|doc| doc.get("uri"))
            .and_then(Value::as_str)
            .and_then(uri_to_path);
        if let Some(path) = path
            && let Some(retry) = completions_with_stub(state, &path, offset)
            && !retry.is_empty()
        {
            items = retry;
        }
    }
    let mut out: Vec<Value> = Vec::new();
    let mut idx = 0usize;
    while idx < items.len() {
        match items.get(idx) {
            Some(item) => out.push(json!({
                "label": item.0,
                "kind": completion_kind_code(item.1)
            })),
            None => break,
        }
        idx += 1;
    }
    Value::Array(out)
}

// Whole-document formatting through the same `format_source` the `cinnabar
// fmt` subcommand uses, so the editor and the CLI cannot disagree about what
// formatted source looks like.
//
// The open buffer is the input, not the file on disk: formatting must apply to
// what the user is looking at, including unsaved edits.  Formatting is
// deliberately independent of analysis -- it is pure text in, text out, so it
// still works on a buffer the front-end has rejected, which is exactly when
// reformatting tends to be asked for.
fn on_formatting(state: &ServerState, params: &Value) -> Value {
    let uri = match params.get("textDocument").and_then(|doc| doc.get("uri")).and_then(Value::as_str)
    {
        Some(value) => value,
        None => return Value::Null,
    };
    let path = match uri_to_path(uri) {
        Some(value) => value,
        None => return Value::Null,
    };
    let source = match state.docs.iter().find(|doc| doc.0 == path) {
        Some(doc) => doc.1.clone(),
        None => return Value::Null,
    };
    let formatted = format_source(&source);
    // An unchanged buffer returns no edits rather than a no-op replacement of
    // the whole document, which would otherwise dirty the file and reset the
    // cursor every time the editor formats on save.
    if formatted == source {
        return Value::Array(Vec::new());
    }
    let (end_line, end_character) = offset_to_position(&source, source.len() as i64);
    Value::Array(vec![json!({
        "range": {
            "start": { "line": 0, "character": 0 },
            "end": { "line": end_line, "character": end_character }
        },
        "newText": formatted
    })])
}

fn on_signature_help(state: &ServerState, params: &Value) -> Value {
    let (analysis, file, offset) = match positional(state, params) {
        Some(found) => found,
        None => return Value::Null,
    };
    match signature_help(analysis, file, offset) {
        Some(info) => {
            let mut params_json: Vec<Value> = Vec::new();
            let mut idx = 0usize;
            while idx < info.params.len() {
                match info.params.get(idx) {
                    Some(label) => params_json.push(json!({ "label": label })),
                    None => break,
                }
                idx += 1;
            }
            json!({
                "signatures": [{ "label": info.label, "parameters": params_json }],
                "activeSignature": 0,
                "activeParameter": info.active
            })
        }
        None => Value::Null,
    }
}

fn on_code_lens(state: &ServerState, params: &Value) -> Value {
    let uri = match params
        .get("textDocument")
        .and_then(|doc| doc.get("uri"))
        .and_then(|value| value.as_str())
    {
        Some(value) => value,
        None => return Value::Array(Vec::new()),
    };
    let path = match uri_to_path(uri) {
        Some(value) => value,
        None => return Value::Array(Vec::new()),
    };
    let entry = entry_of_doc(state, &path);
    let analysis = match completed_analysis(state, &entry) {
        Some(value) => value,
        None => return Value::Array(Vec::new()),
    };
    let file = file_id_of(analysis, &path);
    if file == NONE_ID {
        return Value::Array(Vec::new());
    }
    let mut lenses: Vec<Value> = Vec::new();
    let mut idx = 0usize;
    while idx < analysis.notes.len() {
        match analysis.notes.get(idx) {
            Some(note) => {
                if note.2 == file {
                    // Each lens carries the full explanation group for its
                    // diagnostic, not only its own note, so a client renders
                    // the binding, consuming and live spans from one payload.
                    lenses.push(json!({
                        "range": range_json(analysis, note.2, note.3, note.4),
                        "command": {
                            "title": note.1,
                            "command": "cinnabar.showExplanation",
                            "arguments": [explanation_json(analysis, note.0, idx)]
                        }
                    }));
                }
            }
            None => break,
        }
        idx += 1;
    }
    Value::Array(lenses)
}

// One diagnostic and every note attached to it, in the order the checker
// raised them, with `focus` naming the note whose lens was clicked.  Each
// note reports the stage's own `kind` alongside its prose, so a consumer
// classifies a span by what the borrow checker called it rather than by
// recognizing the wording of a sentence that is free to change.
fn explanation_json(analysis: &Analysis, diag_idx: i64, focus_note: usize) -> Value {
    let diagnostic = match analysis.errors.get(diag_idx as usize) {
        Some(error) => json!({
            "message": error.0,
            "location": location_json(analysis, error.1, error.2, error.3)
        }),
        None => Value::Null,
    };
    let mut explanations: Vec<Value> = Vec::new();
    let mut focus = NONE_ID;
    let mut idx = 0usize;
    while idx < analysis.notes.len() {
        match analysis.notes.get(idx) {
            Some(note) => {
                if note.0 == diag_idx {
                    if idx == focus_note {
                        focus = explanations.len() as i64;
                    }
                    explanations.push(json!({
                        "kind": note_kind_name(note.5),
                        "message": note.1,
                        "location": location_json(analysis, note.2, note.3, note.4)
                    }));
                }
            }
            None => break,
        }
        idx += 1;
    }
    json!({
        "format": "cinnabar.explanation.v1",
        "diagnostic": diagnostic,
        "explanations": explanations,
        "focus": focus
    })
}

// The (path, analysis, file id) behind a file-scoped (non-positional)
// request, or None when the params don't name a file this server has an
// up-to-date analysis for. Mirrors `positional` minus the offset.
fn file_scoped<'state>(state: &'state ServerState, params: &Value) -> Option<(&'state Analysis, i64)> {
    let uri = params.get("textDocument")?.get("uri")?.as_str()?;
    let path = uri_to_path(uri)?;
    let entry = entry_of_doc(state, &path);
    let analysis = completed_analysis(state, &entry)?;
    let file = file_id_of(analysis, &path);
    if file == NONE_ID {
        return None;
    }
    Some((analysis, file))
}

fn on_folding_range(state: &ServerState, params: &Value) -> Value {
    let (analysis, file) = match file_scoped(state, params) {
        Some(found) => found,
        None => return Value::Array(Vec::new()),
    };
    let text = file_text_of(analysis, file);
    let mut out: Vec<Value> = Vec::new();
    let mut idx = 0usize;
    let ranges = folding_ranges(analysis, file);
    while idx < ranges.len() {
        match ranges.get(idx) {
            Some((start, end)) => {
                let start_pos = offset_to_position(&text, *start);
                let end_pos = offset_to_position(&text, *end);
                if end_pos.0 > start_pos.0 {
                    out.push(json!({ "startLine": start_pos.0, "endLine": end_pos.0 }));
                }
            }
            None => break,
        }
        idx += 1;
    }
    Value::Array(out)
}

fn document_symbol_json(analysis: &Analysis, info: &SymbolInfo) -> Value {
    let mut node = json!({
        "name": info.name,
        "kind": info.kind,
        "range": range_json(analysis, info.span.0, info.span.1, info.span.2),
        "selectionRange": range_json(
            analysis,
            info.selection_span.0,
            info.selection_span.1,
            info.selection_span.2
        )
    });
    if !info.detail.is_empty() {
        node["detail"] = json!(info.detail);
    }
    if !info.children.is_empty() {
        let mut children: Vec<Value> = Vec::new();
        let mut idx = 0usize;
        while idx < info.children.len() {
            match info.children.get(idx) {
                Some(child) => children.push(document_symbol_json(analysis, child)),
                None => break,
            }
            idx += 1;
        }
        node["children"] = Value::Array(children);
    }
    node
}

fn on_document_symbol(state: &ServerState, params: &Value) -> Value {
    let (analysis, file) = match file_scoped(state, params) {
        Some(found) => found,
        None => return Value::Array(Vec::new()),
    };
    let symbols = document_symbols(analysis, file);
    let mut out: Vec<Value> = Vec::new();
    let mut idx = 0usize;
    while idx < symbols.len() {
        match symbols.get(idx) {
            Some(info) => out.push(document_symbol_json(analysis, info)),
            None => break,
        }
        idx += 1;
    }
    Value::Array(out)
}

// Every currently open root's analysis carries the full module graph it
// reached, so a workspace search asks each one and concatenates -- there is
// no single `Analysis` that already spans every open root at once.
fn on_workspace_symbol(state: &ServerState, params: &Value) -> Value {
    let query = params.get("query").and_then(Value::as_str).unwrap_or("");
    let mut out: Vec<Value> = Vec::new();
    let mut idx = 0usize;
    while idx < state.completed.len() {
        match state.completed.get(idx) {
            Some(result) => {
                let analysis = &result.analysis;
                let symbols = workspace_symbols(analysis, query);
                let mut s_idx = 0usize;
                while s_idx < symbols.len() {
                    match symbols.get(s_idx) {
                        Some(info) => {
                            if let Some(location) =
                                location_json(analysis, info.span.0, info.span.1, info.span.2)
                            {
                                out.push(json!({
                                    "name": info.name,
                                    "kind": info.kind,
                                    "location": location
                                }));
                            }
                        }
                        None => break,
                    }
                    s_idx += 1;
                }
            }
            None => break,
        }
        idx += 1;
    }
    Value::Array(out)
}

fn workspace_edit_json(analysis: &Analysis, edits: &[(i64, i64, i64, String)]) -> Value {
    let mut by_uri: Vec<(String, Vec<Value>)> = Vec::new();
    let mut idx = 0usize;
    while idx < edits.len() {
        match edits.get(idx) {
            Some((edit_file, start, end, new_text)) => {
                if let Some(entry) = analysis.files.get(*edit_file as usize) {
                    let uri = path_to_uri(&entry.0);
                    let text_edit = json!({
                        "range": range_json(analysis, *edit_file, *start, *end),
                        "newText": new_text
                    });
                    match by_uri.iter_mut().find(|pair| pair.0 == uri) {
                        Some(pair) => pair.1.push(text_edit),
                        None => by_uri.push((uri, vec![text_edit])),
                    }
                }
            }
            None => break,
        }
        idx += 1;
    }
    let mut changes = serde_json::Map::new();
    let mut u_idx = 0usize;
    while u_idx < by_uri.len() {
        match by_uri.get(u_idx) {
            Some((uri, items)) => {
                changes.insert(uri.clone(), Value::Array(items.clone()));
            }
            None => break,
        }
        u_idx += 1;
    }
    json!({ "changes": changes })
}

fn on_prepare_rename(state: &ServerState, params: &Value) -> Value {
    let (analysis, file, offset) = match positional(state, params) {
        Some(found) => found,
        None => return Value::Null,
    };
    match prepare_rename(analysis, file, offset) {
        Some(span) => range_json(analysis, span.0, span.1, span.2),
        None => Value::Null,
    }
}

fn on_rename(state: &ServerState, params: &Value) -> Value {
    let (analysis, file, offset) = match positional(state, params) {
        Some(found) => found,
        None => return Value::Null,
    };
    let new_name = match params.get("newName").and_then(Value::as_str) {
        Some(value) => value,
        None => return Value::Null,
    };
    match rename_edits(analysis, file, offset, new_name) {
        Some(edits) => workspace_edit_json(analysis, &edits),
        None => Value::Null,
    }
}

fn on_semantic_tokens_full(state: &ServerState, params: &Value) -> Value {
    let (analysis, file) = match file_scoped(state, params) {
        Some(found) => found,
        None => return json!({ "data": [] }),
    };
    let text = file_text_of(analysis, file);
    let tokens = semantic_tokens(analysis, file);
    let mut data: Vec<i64> = Vec::new();
    let mut prev_line = 0i64;
    let mut prev_char = 0i64;
    let mut idx = 0usize;
    while idx < tokens.len() {
        match tokens.get(idx) {
            Some((start, end, token_type)) => {
                let (line, character) = offset_to_position(&text, *start);
                let delta_line = line - prev_line;
                let delta_char = if delta_line == 0 { character - prev_char } else { character };
                data.push(delta_line);
                data.push(delta_char);
                data.push(*end - *start);
                data.push(*token_type);
                data.push(0);
                prev_line = line;
                prev_char = character;
            }
            None => break,
        }
        idx += 1;
    }
    json!({ "data": data })
}

fn on_inlay_hint(state: &ServerState, params: &Value) -> Value {
    let (analysis, file) = match file_scoped(state, params) {
        Some(found) => found,
        None => return Value::Array(Vec::new()),
    };
    let text = file_text_of(analysis, file);
    let hints = inlay_hints(analysis, file);
    let mut out: Vec<Value> = Vec::new();
    let mut idx = 0usize;
    while idx < hints.len() {
        match hints.get(idx) {
            Some((offset, label)) => {
                let (line, character) = offset_to_position(&text, *offset);
                out.push(json!({
                    "position": { "line": line, "character": character },
                    "label": label,
                    "kind": 1
                }));
            }
            None => break,
        }
        idx += 1;
    }
    Value::Array(out)
}

fn on_code_action(state: &ServerState, params: &Value) -> Value {
    let (analysis, file) = match file_scoped(state, params) {
        Some(found) => found,
        None => return Value::Array(Vec::new()),
    };
    let text = file_text_of(analysis, file);
    let range = match params.get("range") {
        Some(value) => value,
        None => return Value::Array(Vec::new()),
    };
    let start_line = range.get("start").and_then(|p| p.get("line")).and_then(Value::as_i64).unwrap_or(0);
    let start_char =
        range.get("start").and_then(|p| p.get("character")).and_then(Value::as_i64).unwrap_or(0);
    let end_line = range.get("end").and_then(|p| p.get("line")).and_then(Value::as_i64).unwrap_or(0);
    let end_char = range.get("end").and_then(|p| p.get("character")).and_then(Value::as_i64).unwrap_or(0);
    let range_start = position_to_offset(&text, start_line, start_char);
    let range_end = position_to_offset(&text, end_line, end_char);
    let fixes = code_actions(analysis, file, range_start, range_end);
    let mut out: Vec<Value> = Vec::new();
    let mut idx = 0usize;
    while idx < fixes.len() {
        match fixes.get(idx) {
            Some(fix) => out.push(json!({
                "title": fix.title,
                "kind": "quickfix",
                "edit": workspace_edit_json(analysis, &fix.edits)
            })),
            None => break,
        }
        idx += 1;
    }
    Value::Array(out)
}

// ---------------------------------------------------------------------------
// Notifications / document sync
// ---------------------------------------------------------------------------

fn handle_notification(
    connection: &Connection,
    state: &mut ServerState,
    note: Notification,
) -> Result<(), String> {
    let method = note.method.clone();
    if method == "textDocument/didOpen" {
        let uri_path = note
            .params
            .get("textDocument")
            .and_then(|doc| doc.get("uri"))
            .and_then(|uri| uri.as_str())
            .and_then(uri_to_path);
        let text = note
            .params
            .get("textDocument")
            .and_then(|doc| doc.get("text"))
            .and_then(|text| text.as_str())
            .map(|text| text.to_string());
        if let (Some(path), Some(content)) = (uri_path, text) {
            set_doc(state, &path, content);
            let entry = register_document(state, &path);
            schedule_analysis(state, &entry, DIAGNOSTIC_DEBOUNCE_MS);
        }
        return Ok(());
    }
    if method == "textDocument/didChange" {
        let uri_path = note
            .params
            .get("textDocument")
            .and_then(|doc| doc.get("uri"))
            .and_then(|uri| uri.as_str())
            .and_then(uri_to_path);
        // Full-document sync: the last content change carries the whole text.
        let text = note
            .params
            .get("contentChanges")
            .and_then(|changes| changes.as_array())
            .and_then(|changes| changes.last())
            .and_then(|change| change.get("text"))
            .and_then(|text| text.as_str())
            .map(|text| text.to_string());
        if let (Some(path), Some(content)) = (uri_path, text) {
            set_doc(state, &path, content);
            let entry = entry_of_doc(state, &path);
            schedule_analysis(state, &entry, DIAGNOSTIC_DEBOUNCE_MS);
        }
        return Ok(());
    }
    if method == "textDocument/didSave" {
        let uri_path = note
            .params
            .get("textDocument")
            .and_then(|doc| doc.get("uri"))
            .and_then(|uri| uri.as_str())
            .and_then(uri_to_path);
        if let Some(path) = uri_path {
            let entry = entry_of_doc(state, &path);
            schedule_analysis(state, &entry, 0);
        }
        return Ok(());
    }
    if method == "textDocument/didClose" {
        let uri_path = note
            .params
            .get("textDocument")
            .and_then(|doc| doc.get("uri"))
            .and_then(|uri| uri.as_str())
            .and_then(uri_to_path);
        if let Some(path) = uri_path {
            let entry = entry_of_doc(state, &path);
            remove_doc(state, &path);
            remove_doc_entry(state, &path);
            if entry == path {
                close_root(connection, state, &entry)?;
            } else {
                let cleared: Vec<Value> = Vec::new();
                send_diagnostics(connection, &path_to_uri(&path), cleared)?;
                schedule_analysis(state, &entry, 0);
            }
        }
        return Ok(());
    }
    // initialized, setTrace, cancelRequest, exit and anything else need no
    // action from this server.
    Ok(())
}

fn entry_of_doc(state: &ServerState, path: &str) -> String {
    let mut idx = 0usize;
    while idx < state.doc_entries.len() {
        match state.doc_entries.get(idx) {
            Some(pair) => {
                if pair.0 == path {
                    return pair.1.clone();
                }
            }
            None => break,
        }
        idx += 1;
    }
    path.to_string()
}

fn register_document(state: &mut ServerState, path: &str) -> String {
    let existing = entry_of_doc(state, path);
    if existing != path {
        return existing;
    }
    if state.roots.contains(&path.to_string()) {
        return path.to_string();
    }
    // A file that belongs to no project is the ordinary case for an editor —
    // a scratch buffer, a fixture opened on its own — so the failure is the
    // answer "no project", not something to report to the user.
    if let Ok(entry_path) = project::entry_for_source(std::path::Path::new(path)) {
        let entry = entry_path.to_string_lossy().to_string();
        state.doc_entries.push((path.to_string(), entry.clone()));
        if !state.roots.contains(&entry) {
            state.roots.push(entry.clone());
        }
        return entry;
    }
    let uri = path_to_uri(path);
    let mut idx = 0usize;
    while idx < state.published.len() {
        match state.published.get(idx) {
            Some(record) => {
                if record.1.contains(&uri) {
                    let entry = record.0.clone();
                    state.doc_entries.push((path.to_string(), entry.clone()));
                    return entry;
                }
            }
            None => break,
        }
        idx += 1;
    }
    let entry = path.to_string();
    state.roots.push(entry.clone());
    state.doc_entries.push((entry.clone(), entry.clone()));
    entry
}

// Reconcile open-order differences from the compiler's actual module graph.
// If this entry contains roots that were opened earlier as standalone files,
// it becomes their owner.  No import or path semantics are reconstructed here:
// membership comes exclusively from module_loader's analyzed file set.
fn reconcile_root_graph(state: &mut ServerState, entry: &str, analysis: &Analysis) {
    let mut adopted: Vec<String> = Vec::new();
    let mut idx = 0usize;
    while idx < state.roots.len() {
        match state.roots.get(idx) {
            Some(root) => {
                if root != entry && file_id_of(analysis, root) != NONE_ID {
                    adopted.push(root.clone());
                }
            }
            None => break,
        }
        idx += 1;
    }
    idx = 0;
    while idx < adopted.len() {
        match adopted.get(idx) {
            Some(root) => invalidate_analysis(state, root),
            None => break,
        }
        idx += 1;
    }
    idx = 0;
    while idx < state.doc_entries.len() {
        let owner = match state.doc_entries.get(idx) {
            Some(pair) => pair.1.clone(),
            None => break,
        };
        if adopted.contains(&owner)
            && let Some(pair) = state.doc_entries.get_mut(idx)
        {
            pair.1 = entry.to_string();
        }
        idx += 1;
    }
    let mut roots: Vec<String> = Vec::new();
    while let Some(root) = state.roots.pop() {
        if !adopted.contains(&root) {
            roots.push(root);
        }
    }
    state.roots = roots;
    if !adopted.is_empty() {
        transfer_publications(state, entry, &adopted);
    }
}

fn transfer_publications(state: &mut ServerState, entry: &str, adopted: &[String]) {
    let mut records: Vec<(String, Vec<String>)> = Vec::new();
    let mut owned: Vec<String> = Vec::new();
    while let Some(record) = state.published.pop() {
        if record.0 == entry || adopted.contains(&record.0) {
            let mut uri_idx = 0usize;
            while uri_idx < record.1.len() {
                match record.1.get(uri_idx) {
                    Some(uri) => {
                        if !owned.contains(uri) {
                            owned.push(uri.clone());
                        }
                    }
                    None => break,
                }
                uri_idx += 1;
            }
        } else {
            records.push(record);
        }
    }
    records.push((entry.to_string(), owned));
    state.published = records;
}

fn remove_doc_entry(state: &mut ServerState, path: &str) {
    let mut kept: Vec<(String, String)> = Vec::new();
    while let Some(pair) = state.doc_entries.pop() {
        if pair.0 != path {
            kept.push(pair);
        }
    }
    state.doc_entries = kept;
}

fn close_root(connection: &Connection, state: &mut ServerState, entry: &str) -> Result<(), String> {
    invalidate_analysis(state, entry);
    let mut roots: Vec<String> = Vec::new();
    while let Some(root) = state.roots.pop() {
        if root != entry {
            roots.push(root);
        }
    }
    state.roots = roots;
    let mut remap: Vec<String> = Vec::new();
    let mut mappings: Vec<(String, String)> = Vec::new();
    while let Some(pair) = state.doc_entries.pop() {
        if pair.1 == entry {
            if pair.0 != entry {
                remap.push(pair.0);
            }
        } else {
            mappings.push(pair);
        }
    }
    state.doc_entries = mappings;
    let mut records: Vec<(String, Vec<String>)> = Vec::new();
    let mut closing_uris: Vec<String> = Vec::new();
    while let Some(record) = state.published.pop() {
        if record.0 == entry {
            closing_uris = record.1;
        } else {
            records.push(record);
        }
    }
    let mut idx = 0usize;
    while idx < closing_uris.len() {
        match closing_uris.get(idx) {
            Some(uri) => {
                if !uri_owned_by(&records, uri) {
                    let cleared: Vec<Value> = Vec::new();
                    send_diagnostics(connection, uri, cleared)?;
                }
            }
            None => break,
        }
        idx += 1;
    }
    state.published = records;
    while let Some(path) = remap.pop() {
        let new_entry = register_document(state, &path);
        schedule_analysis(state, &new_entry, 0);
    }
    Ok(())
}

fn current_generation(state: &ServerState, path: &str) -> i64 {
    let mut idx = 0usize;
    while idx < state.generations.len() {
        match state.generations.get(idx) {
            Some(entry) => {
                if entry.0 == path {
                    return entry.1;
                }
            }
            None => break,
        }
        idx += 1;
    }
    0
}

// A completed analysis is valid only for the same root generation that
// produced it. Document edits advance that generation before scheduling the
// next worker, so stale compiler facts can never answer a positional request.
fn completed_analysis<'state>(state: &'state ServerState, path: &str) -> Option<&'state Analysis> {
    let generation = current_generation(state, path);
    let mut idx = 0usize;
    while idx < state.completed.len() {
        match state.completed.get(idx) {
            Some(result) => {
                if result.path == path && result.generation == generation {
                    return Some(&result.analysis);
                }
            }
            None => break,
        }
        idx += 1;
    }
    None
}

fn retain_completed_analysis(state: &mut ServerState, result: AnalysisResult) {
    let mut idx = 0usize;
    while idx < state.completed.len() {
        let matches_path = match state.completed.get(idx) {
            Some(existing) => existing.path == result.path,
            None => false,
        };
        if matches_path {
            state.completed.remove(idx);
            break;
        }
        idx += 1;
    }
    state.completed.push(result);
}

fn discard_completed_analysis(state: &mut ServerState, path: &str) {
    let mut idx = 0usize;
    while idx < state.completed.len() {
        let matches_path = match state.completed.get(idx) {
            Some(existing) => existing.path == path,
            None => false,
        };
        if matches_path {
            state.completed.remove(idx);
            return;
        }
        idx += 1;
    }
}

fn advance_generation(state: &mut ServerState, path: &str) -> i64 {
    let mut idx = 0usize;
    while idx < state.generations.len() {
        let matches_path = match state.generations.get(idx) {
            Some(entry) => entry.0 == path,
            None => false,
        };
        if matches_path
            && let Some(entry) = state.generations.get_mut(idx)
        {
                entry.1 += 1;
                return entry.1;
        }
        idx += 1;
    }
    state.generations.push((path.to_string(), 1));
    1
}

fn invalidate_analysis(state: &mut ServerState, path: &str) {
    advance_generation(state, path);
    discard_completed_analysis(state, path);
    let mut idx = 0usize;
    while idx < state.pending.len() {
        let matches_path = match state.pending.get(idx) {
            Some(entry) => entry.0 == path,
            None => false,
        };
        if matches_path {
            state.pending.remove(idx);
        } else {
            idx += 1;
        }
    }
}

fn schedule_analysis(state: &mut ServerState, path: &str, delay_ms: u64) {
    invalidate_analysis(state, path);
    let generation = current_generation(state, path);
    state.pending.push((
        path.to_string(),
        generation,
        Instant::now() + Duration::from_millis(delay_ms),
    ));
}

fn start_due_analyses(state: &mut ServerState) {
    if state.running_path.is_some() {
        return;
    }
    let now = Instant::now();
    let mut due_idx: Option<usize> = None;
    let mut idx = 0usize;
    while idx < state.pending.len() {
        let due = match state.pending.get(idx) {
            Some(entry) => entry.2 <= now,
            None => false,
        };
        if due {
            due_idx = Some(idx);
            break;
        }
        idx += 1;
    }
    if let Some(selected_idx) = due_idx {
        let selected = state.pending.remove(selected_idx);
        let path = selected.0;
        let generation = selected.1;
        let docs = state.docs.clone();
        let tx = state.analysis_tx.clone();
        state.running_path = Some(path.clone());
        std::thread::spawn(move || {
            let analysis = analyze(&path, &docs);
            tx.send(AnalysisResult { path, generation, analysis }).is_ok()
        });
    }
}

fn publish_completed(connection: &Connection, state: &mut ServerState) -> Result<(), String> {
    while let Ok(result) = state.analysis_rx.try_recv() {
        let finished_running = state
            .running_path
            .as_ref()
            .is_some_and(|path| path == &result.path);
        if finished_running {
            state.running_path = None;
        }
        if current_generation(state, &result.path) == result.generation {
            publish_analysis(connection, state, &result.path, &result.analysis)?;
            retain_completed_analysis(state, result);
        }
    }
    Ok(())
}

fn set_doc(state: &mut ServerState, path: &str, content: String) {
    let mut idx = 0usize;
    while idx < state.docs.len() {
        let matches_path = match state.docs.get(idx) {
            Some(entry) => entry.0 == path,
            None => false,
        };
        if matches_path {
            if let Some(entry) = state.docs.get_mut(idx) {
                entry.1 = content;
            }
            return;
        }
        idx += 1;
    }
    state.docs.push((path.to_string(), content));
}

fn remove_doc(state: &mut ServerState, path: &str) {
    let mut kept: Vec<(String, String)> = Vec::new();
    while let Some(entry) = state.docs.pop() {
        if entry.0 != path {
            kept.push(entry);
        }
    }
    state.docs = kept;
}

fn severity_error() -> i64 {
    1
}

fn publish_analysis(
    connection: &Connection,
    state: &mut ServerState,
    entry_path: &str,
    analysis: &Analysis,
) -> Result<(), String> {
    reconcile_root_graph(state, entry_path, analysis);
    forward_source_less_diagnostics(connection, state, entry_path, analysis)?;
    let mut fresh: Vec<String> = Vec::new();
    let mut file = 0i64;
    while (file as usize) < analysis.files.len() {
        let path = match analysis.files.get(file as usize) {
            Some(pair) => pair.0.clone(),
            None => break,
        };
        let uri = path_to_uri(&path);
        let diags = file_diagnostics(analysis, file);
        send_diagnostics(connection, &uri, diags)?;
        fresh.push(uri);
        file += 1;
    }
    // Replace only this root's publication set.  Another open root may own
    // the same URI, so a stale URI is cleared only when no remaining root
    // still publishes it.
    let mut prior: Vec<String> = Vec::new();
    let mut records: Vec<(String, Vec<String>)> = Vec::new();
    while let Some(record) = state.published.pop() {
        if record.0 == entry_path {
            prior = record.1;
        } else {
            records.push(record);
        }
    }
    let mut idx = 0usize;
    while idx < prior.len() {
        match prior.get(idx) {
            Some(uri) => {
                if !fresh.contains(uri) && !uri_owned_by(&records, uri) {
                    let cleared: Vec<Value> = Vec::new();
                    send_diagnostics(connection, uri, cleared)?;
                }
            }
            None => break,
        }
        idx += 1;
    }
    records.push((entry_path.to_string(), fresh));
    state.published = records;
    Ok(())
}

// A diagnostic carrying `NO_FILE` genuinely has no source location — the
// entry file itself could not be read, for example — so the per-file filter
// in `file_diagnostics` can never select it and it used to vanish entirely,
// leaving an unreadable project looking clean and error-free. It is
// forwarded as a `window/showMessage` error instead, which is honest about
// the diagnostic having no location to attach to. Each message fires when
// it first appears for a root and again only after it has gone away, not on
// every republish of the same analysis.
fn forward_source_less_diagnostics(
    connection: &Connection,
    state: &mut ServerState,
    entry_path: &str,
    analysis: &Analysis,
) -> Result<(), String> {
    let mut current: Vec<String> = Vec::new();
    let mut idx = 0usize;
    while idx < analysis.errors.len() {
        let diag = match analysis.errors.get(idx) {
            Some(diag) => diag,
            None => break,
        };
        if diag.1 == NO_FILE && !current.contains(&diag.0) {
            current.push(diag.0.clone());
        }
        idx += 1;
    }
    let mut previous: Vec<String> = Vec::new();
    let mut records: Vec<(String, Vec<String>)> = Vec::new();
    while let Some(record) = state.source_less.pop() {
        if record.0 == entry_path {
            previous = record.1;
        } else {
            records.push(record);
        }
    }
    idx = 0;
    while idx < current.len() {
        match current.get(idx) {
            Some(message) => {
                if !previous.contains(message) {
                    show_message(connection, message)?;
                }
            }
            None => break,
        }
        idx += 1;
    }
    if !current.is_empty() {
        records.push((entry_path.to_string(), current));
    }
    state.source_less = records;
    Ok(())
}

fn uri_owned_by(records: &[(String, Vec<String>)], uri: &str) -> bool {
    let mut idx = 0usize;
    while idx < records.len() {
        match records.get(idx) {
            Some(record) => {
                if record.1.contains(&uri.to_string()) {
                    return true;
                }
            }
            None => break,
        }
        idx += 1;
    }
    false
}

fn file_diagnostics(analysis: &Analysis, file: i64) -> Vec<Value> {
    let mut out: Vec<Value> = Vec::new();
    let mut idx = 0usize;
    while idx < analysis.errors.len() {
        let diag = match analysis.errors.get(idx) {
            Some(diag) => diag,
            None => break,
        };
        if diag.1 == file {
            let mut related: Vec<Value> = Vec::new();
            let mut note_idx = 0usize;
            while note_idx < analysis.notes.len() {
                match analysis.notes.get(note_idx) {
                    Some(note) => {
                        if note.0 == idx as i64
                            && note.2 != NO_FILE
                            && let Some(location) = location_json(analysis, note.2, note.3, note.4)
                        {
                            related.push(json!({ "location": location, "message": note.1 }));
                        }
                    }
                    None => break,
                }
                note_idx += 1;
            }
            let mut diag_json = json!({
                "range": range_json(analysis, file, diag.2, diag.3),
                "severity": severity_error(),
                "source": "cinnabar",
                "message": diag.0
            });
            if !related.is_empty()
                && let Some(object) = diag_json.as_object_mut()
            {
                object.insert("relatedInformation".to_string(), Value::Array(related));
            }
            out.push(diag_json);
        }
        idx += 1;
    }
    out
}

fn send_diagnostics(connection: &Connection, uri: &str, diagnostics: Vec<Value>) -> Result<(), String> {
    let note = Notification {
        method: "textDocument/publishDiagnostics".to_string(),
        params: json!({ "uri": uri, "diagnostics": diagnostics }),
    };
    connection
        .sender
        .send(Message::Notification(note))
        .map_err(|err| format!("send diagnostics: {}", err))
}

// ---------------------------------------------------------------------------
// file:// URI <-> path
// ---------------------------------------------------------------------------

fn hex_value(byte: u8) -> Option<u8> {
    if byte.is_ascii_digit() {
        return Some(byte - b'0');
    }
    if byte.is_ascii_hexdigit() && byte.is_ascii_lowercase() {
        return Some(byte - b'a' + 10);
    }
    if byte.is_ascii_hexdigit() && byte.is_ascii_uppercase() {
        return Some(byte - b'A' + 10);
    }
    None
}

fn percent_decode(text: &str) -> String {
    let bytes = text.as_bytes();
    let mut out: Vec<u8> = Vec::new();
    let mut idx = 0usize;
    while idx < bytes.len() {
        let byte = match bytes.get(idx) {
            Some(value) => *value,
            None => break,
        };
        if byte == b'%' && idx + 2 <= bytes.len() {
            let high = bytes.get(idx + 1).and_then(|value| hex_value(*value));
            let low = bytes.get(idx + 2).and_then(|value| hex_value(*value));
            if let (Some(hi), Some(lo)) = (high, low) {
                out.push(hi * 16 + lo);
                idx += 3;
                continue;
            }
        }
        out.push(byte);
        idx += 1;
    }
    String::from_utf8_lossy(&out).to_string()
}

fn percent_encode_path(path: &str) -> String {
    let mut out = String::new();
    for byte in path.as_bytes() {
        let ch = *byte as char;
        if byte.is_ascii_alphanumeric() || "/:._~-".contains(ch) {
            out.push(ch);
        } else if ch == '\\' {
            out.push('/');
        } else {
            out.push_str(&format!("%{:02X}", byte));
        }
    }
    out
}

/// A file:// URI to a local file-system path, or None for other schemes.
fn uri_to_path(uri: &str) -> Option<String> {
    let rest = uri.strip_prefix("file://")?;
    // Strip an empty authority; a non-empty authority (remote host) is not
    // a local file.  "file:///..." leaves the absolute path (minus its
    // leading slash on Windows drive paths).
    let path_part = rest.strip_prefix('/')?;
    let decoded = percent_decode(path_part);
    // Windows drive path: "C:/..." after decoding.  A path that does not
    // look like a drive keeps its leading slash (POSIX).
    let is_drive = {
        let bytes = decoded.as_bytes();
        bytes.len() >= 2
            && bytes.first().is_some_and(|byte| byte.is_ascii_alphabetic())
            && bytes.get(1).is_some_and(|byte| *byte == b':')
    };
    if is_drive {
        // The same normalization `project` applies after canonicalizing:
        // editors spell the drive letter in either case, while the paths the
        // manifest loader stores are upper-cased, and the module loader's
        // overlay lookup compares the two. On an already-plain path this
        // changes nothing but the drive letter.
        Some(project::comparable_path(std::path::Path::new(&decoded)).to_string_lossy().to_string())
    } else {
        Some(format!("/{}", decoded))
    }
}

/// A local file-system path to a file:// URI.
fn path_to_uri(path: &str) -> String {
    let normalized = path.replace('\\', "/");
    if normalized.starts_with('/') {
        format!("file://{}", percent_encode_path(&normalized))
    } else {
        format!("file:///{}", percent_encode_path(&normalized))
    }
}

#[cfg(test)]
mod tests {
    use super::{path_to_uri, start_due_analyses, uri_to_path, AnalysisResult, ServerState};
    use std::sync::mpsc::channel;
    use std::time::Instant;

    #[test]
    fn analysis_scheduler_allows_only_one_active_frontend() {
        let (analysis_tx, analysis_rx) = channel::<AnalysisResult>();
        let now = Instant::now();
        let mut state = ServerState {
            docs: Vec::new(),
            published: Vec::new(),
            roots: Vec::new(),
            doc_entries: Vec::new(),
            generations: vec![("first.cnb".to_string(), 1), ("second.cnb".to_string(), 1)],
            pending: vec![
                ("first.cnb".to_string(), 1, now),
                ("second.cnb".to_string(), 1, now),
            ],
            running_path: None,
            analysis_tx,
            analysis_rx,
            completed: Vec::new(),
            source_less: Vec::new(),
        };

        start_due_analyses(&mut state);
        assert!(state.running_path.is_some());
        assert_eq!(state.pending.len(), 1);

        start_due_analyses(&mut state);
        assert!(state.running_path.is_some());
        assert_eq!(state.pending.len(), 1, "a second full analysis started concurrently");
    }

    #[test]
    fn windows_file_uri_roundtrips_reserved_characters() {
        let path = "C:\\Users\\Cinnabar Dev\\source#one.cnb";
        let uri = path_to_uri(path);
        assert_eq!(uri, "file:///C:/Users/Cinnabar%20Dev/source%23one.cnb");
        assert_eq!(uri_to_path(&uri), Some("C:/Users/Cinnabar Dev/source#one.cnb".to_string()));
    }

    #[test]
    fn posix_file_uri_roundtrips_reserved_characters() {
        let path = "/tmp/Cinnabar Dev/source#one.cnb";
        let uri = path_to_uri(path);
        assert_eq!(uri, "file:///tmp/Cinnabar%20Dev/source%23one.cnb");
        assert_eq!(uri_to_path(&uri), Some(path.to_string()));
    }

    #[test]
    fn remote_file_authority_is_not_treated_as_local() {
        assert_eq!(uri_to_path("file://server/share/source.cnb"), None);
    }

    // VS Code sends drive letters lower-cased ("file:///c%3A/..."), while the
    // manifest loader stores canonicalized paths with the drive upper-cased.
    // The decoded path must land in the canonical spelling or the module
    // loader's overlay never matches the open buffer.
    #[test]
    fn lowercase_drive_uri_decodes_to_canonical_drive_case() {
        assert_eq!(
            uri_to_path("file:///c%3A/project/main.cnb"),
            Some("C:/project/main.cnb".to_string())
        );
    }
}
