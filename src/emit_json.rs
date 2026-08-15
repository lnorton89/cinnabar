//! The machine-readable renderings behind `--emit-json`.
//!
//! Every introspection surface the compiler has was written for a terminal:
//! the arena dumps indent, the layout report aligns columns, and diagnostics
//! go through ariadne. A tool that wants those facts — an editor, a
//! playground, a snapshot reviewer — should not have to scrape that text
//! back into structure, so this file owns the second rendering of the same
//! facts and nothing else. It defines the version tag of each document, the
//! shape of a source span, and the diagnostic envelope; the arena rows come
//! from `inspect`, and the layout numbers from `codegen::layout`, because
//! those are the files that already own those facts.
//!
//! A span here carries both the byte offsets the compiler works in and the
//! line/UTF-16-column pair a protocol wants, mapped through the same
//! `analysis::offset_to_position` the language server uses, so an editor and
//! a `--emit-json` consumer cannot disagree about where a diagnostic points.
//!
//! **Invariants:**
//! - Nothing is computed here. A number or name in one of these documents
//!   was established by an earlier stage and is being re-rendered; a fact
//!   this file derived would be a second opinion the human rendering never
//!   agreed to.
//! - `NO_FILE` renders as a null source, never as a location. A fact with no
//!   Cinnabar origin has no line to offer, and a JSON consumer is exactly
//!   the reader most likely to believe a fabricated one.

use crate::analysis::offset_to_position;
use crate::ast::{Diag, Note, NO_FILE};
use serde_json::{json, Value};

/// The parse-only arena, as `--dump-ast --emit-json` emits it.
pub const AST_FORMAT: &str = "cinnabar.ast.v1";

/// The arena with every front-end attachment, as `--dump-typed-ast
/// --emit-json` emits it.
pub const TYPED_AST_FORMAT: &str = "cinnabar.typed-ast.v1";

/// The ABI layout report, as `--print-layout --emit-json` emits it.
pub const LAYOUT_FORMAT: &str = "cinnabar.layout.v1";

/// The diagnostic envelope. Every failing `--emit-json` invocation emits
/// this document, whichever stage produced the diagnostics; a clean one
/// emits it with an empty list.
pub const DIAGNOSTICS_FORMAT: &str = "cinnabar.diagnostics.v1";

/// Render one span as the source object every document shares.
///
/// A span whose file is `NO_FILE` has no source origin at all and renders
/// as null. A span naming a file that is not in the loaded set keeps its
/// offsets and reports a null path, since offsets into a file nobody can
/// read are still true and a made-up path would not be.
pub fn source_json(files: &[(String, String)], file: i64, start: i64, end: i64) -> Value {
    if file == NO_FILE {
        return Value::Null;
    }
    match files.get(file as usize) {
        Some(entry) => {
            let (start_line, start_column) = offset_to_position(&entry.1, start);
            let (end_line, end_column) = offset_to_position(&entry.1, end);
            json!({
                "file_id": file,
                "path": entry.0,
                "start": start,
                "end": end,
                "start_line": start_line,
                "start_column": start_column,
                "end_line": end_line,
                "end_column": end_column
            })
        }
        None => json!({
            "file_id": file,
            "path": Value::Null,
            "start": start,
            "end": end
        }),
    }
}

/// The structured diagnostic envelope: every diagnostic in `errors`, each
/// carrying the notes an earlier stage attached to it.
///
/// The notes are the same rows `--explain-borrow` renders as secondary
/// labels — which paths consume a value, where it was bound, where it was
/// previously moved — so a consumer of this document has the whole
/// explanation the terminal rendering would have shown.
pub fn diagnostics_report(errors: &[Diag], notes: &[Note], files: &[(String, String)]) -> Value {
    let mut diagnostics: Vec<Value> = Vec::new();
    let mut error_idx = 0usize;
    while error_idx < errors.len() {
        let error = match errors.get(error_idx) {
            Some(value) => value,
            None => break,
        };
        diagnostics.push(json!({
            "severity": "error",
            "message": error.0,
            "source": source_json(files, error.1, error.2, error.3),
            "explanations": explanations_of(error_idx as i64, notes, files)
        }));
        error_idx += 1;
    }
    json!({
        "format": DIAGNOSTICS_FORMAT,
        "diagnostics": diagnostics
    })
}

fn explanations_of(diag_idx: i64, notes: &[Note], files: &[(String, String)]) -> Vec<Value> {
    let mut explanations: Vec<Value> = Vec::new();
    let mut note_idx = 0usize;
    while note_idx < notes.len() {
        match notes.get(note_idx) {
            Some(note) => {
                if note.0 == diag_idx {
                    explanations.push(json!({
                        "message": note.1,
                        "source": source_json(files, note.2, note.3, note.4)
                    }));
                }
            }
            None => break,
        }
        note_idx += 1;
    }
    explanations
}

/// The `file_id` to path mapping every arena document carries, so a node's
/// `file` slot can be read without a second load of the module set.
pub fn files_json(files: &[(String, String)]) -> Vec<Value> {
    let mut out: Vec<Value> = Vec::new();
    let mut idx = 0usize;
    while idx < files.len() {
        match files.get(idx) {
            Some(entry) => out.push(json!({ "file_id": idx as i64, "path": entry.0 })),
            None => break,
        }
        idx += 1;
    }
    out
}

/// Serialize one document for standard output.
///
/// The rendering can fail, and a driver that swallowed that would print
/// nothing at all where a consumer expects a document, so the failure is
/// returned as a message for the one place allowed to stringify it.
pub fn render_report(report: &Value) -> Result<String, String> {
    serde_json::to_string_pretty(report)
        .map_err(|render_error| format!("cannot serialize JSON report: {}", render_error))
}
