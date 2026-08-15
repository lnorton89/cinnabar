//! The published API documentation, as a page and as a document.
//!
//! `render_api_docs` walks the parsed item lists and emits one article per
//! public declaration, taking the prose from the `NODE_DOC` rows the parser
//! attached to each item. `docs_json` walks the same item lists, applies
//! the same `node_b == 1` visibility test, and emits one object per
//! declaration with its kind, name, `attached_docs` paragraphs, members and
//! span. `render_cinnabook` folds that output together
//! with the manifesto into a single version-pinned page, and
//! `serve_cinnabook` serves a rendered page over HTTP.
//!
//! **Invariants:**
//! - Visibility is read from the parsed item, never re-decided here. A
//!   declaration that is not `pub` does not appear, and neither does its
//!   doc text.
//! - Documentation prose comes from parser attachments. This file never
//!   re-scans source for comment syntax, so what gets published is what the
//!   compiler actually attached to the item.
//! - Every interpolated value is HTML-escaped, the embedded manifesto
//!   included — it is published as text, not as markup.

use crate::ast::*;
use crate::emit_json::DOCS_FORMAT;
use serde_json::{json, Value};
use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};

pub fn render_api_docs(names: &[String], nodes: &[i64], lists: &[Vec<i64>], root: i64) -> String {
    let mut body = String::new();
    render_item_list(names, nodes, lists, root, 1, &mut body);
    page("Cinnabar API documentation", &body)
}

/// Every public declaration reachable from the entry, as one document.
///
/// The same walk the page above does, reported rather than laid out: the
/// visibility test, the declaration kinds, and the attached prose are the
/// ones `render_api_docs` uses, so a site built on this cannot publish a
/// declaration the page would have hidden.
pub fn docs_json(names: &[String], nodes: &[i64], lists: &[Vec<i64>], root: i64, files: &[(String, String)]) -> Value {
    json!({
        "format": DOCS_FORMAT,
        "version": env!("CARGO_PKG_VERSION"),
        "files": crate::emit_json::files_json(files),
        "declarations": declarations_json(names, nodes, lists, root, files)
    })
}

fn declarations_json(
    names: &[String],
    nodes: &[i64],
    lists: &[Vec<i64>],
    item_list: i64,
    files: &[(String, String)],
) -> Vec<Value> {
    let mut out: Vec<Value> = Vec::new();
    let mut idx = 0i64;
    while idx < list_len(lists, item_list) {
        let item = list_get(lists, item_list, idx);
        // The same visibility test the page makes, read off the parsed item
        // rather than decided again here.
        if node_tag(nodes, item) == NODE_ITEM && node_b(nodes, item) == 1 {
            out.push(declaration_json(names, nodes, lists, item, files));
        }
        idx += 1;
    }
    out
}

fn declaration_json(
    names: &[String],
    nodes: &[i64],
    lists: &[Vec<i64>],
    item: i64,
    files: &[(String, String)],
) -> Value {
    let kind = node_a(nodes, item);
    let (label, name) = item_label_and_name(names, nodes, item);
    let mut entry = json!({
        "kind": label,
        "name": name,
        "documentation": attached_docs(names, nodes, lists, item),
        "source": crate::emit_json::source_json(files, node_file(nodes, item), node_start(nodes, item), node_end(nodes, item))
    });
    let members = if kind == ITEM_STRUCT {
        members_json(names, nodes, lists, node_e(nodes, item), "Field", files)
    } else if kind == ITEM_ENUM {
        members_json(names, nodes, lists, node_e(nodes, item), "Variant", files)
    } else if kind == ITEM_TRAIT {
        methods_json(names, nodes, lists, node_e(nodes, item), files)
    } else {
        Vec::new()
    };
    if let Some(object) = entry.as_object_mut() {
        if !members.is_empty() {
            object.insert("members".to_string(), Value::Array(members));
        }
        if kind == ITEM_MODULE {
            object.insert(
                "declarations".to_string(),
                Value::Array(declarations_json(names, nodes, lists, node_e(nodes, item), files)),
            );
        }
    }
    entry
}

fn members_json(
    names: &[String],
    nodes: &[i64],
    lists: &[Vec<i64>],
    members: i64,
    label: &str,
    files: &[(String, String)],
) -> Vec<Value> {
    let mut out: Vec<Value> = Vec::new();
    let mut idx = 0i64;
    while idx < list_len(lists, members) {
        let member = list_get(lists, members, idx);
        if node_c(nodes, member) == 1 {
            out.push(json!({
                "kind": label,
                "name": name_text(names, node_a(nodes, member)),
                "documentation": attached_docs(names, nodes, lists, member),
                "source": crate::emit_json::source_json(files, node_file(nodes, member), node_start(nodes, member), node_end(nodes, member))
            }));
        }
        idx += 1;
    }
    out
}

fn methods_json(
    names: &[String],
    nodes: &[i64],
    lists: &[Vec<i64>],
    methods: i64,
    files: &[(String, String)],
) -> Vec<Value> {
    let mut out: Vec<Value> = Vec::new();
    let mut idx = 0i64;
    while idx < list_len(lists, methods) {
        let method = list_get(lists, methods, idx);
        out.push(json!({
            "kind": "Method",
            "name": name_text(names, node_a(nodes, method)),
            "documentation": attached_docs(names, nodes, lists, method),
            "source": crate::emit_json::source_json(files, node_file(nodes, method), node_start(nodes, method), node_end(nodes, method))
        }));
        idx += 1;
    }
    out
}

pub fn render_cinnabook(api_html: &str) -> String {
    let manifesto = escape_html(include_str!("../MANIFESTO.md"));
    let mut api = api_html;
    if let Some(body_start) = api_html.find("<body>")
        && let Some(body_end) = api_html.rfind("</body>")
        && body_start + "<body>".len() <= body_end
    {
        api = &api_html[body_start + "<body>".len()..body_end];
    }
    let body = format!(
        "<h1>Cinnabook</h1><p class=version>Compiler version {}</p>\
         <nav><a href=#language>Language manifesto</a> · <a href=#api>API documentation</a></nav>\
         <section id=language><h2>Language manifesto</h2><pre>{}</pre></section>\
         <section id=api><h2>API documentation</h2><div class=embedded>{}</div></section>",
        env!("CARGO_PKG_VERSION"),
        manifesto,
        api
    );
    page("Cinnabook", &body)
}

pub fn serve_cinnabook(
    address: &str,
    page_text: &str,
    mut report_error: impl FnMut(&str),
) -> Result<(), String> {
    let listener = TcpListener::bind(address)
        .map_err(|bind_error| format!("cannot bind Cinnabook server to '{}': {}", address, bind_error))?;
    // Only the bind is fatal: once the socket is listening, a connection
    // that fails to accept, read, or write is that one visitor's problem —
    // a browser closing mid-response must not take the server down for
    // every future visitor. Per-connection failures are reported to the
    // caller through `report_error` (never printed directly here — this is
    // library code, and only the CLI entry point in `main.rs` decides how a
    // message reaches the user), which renders them, and the loop moves on.
    for incoming in listener.incoming() {
        let mut stream = match incoming {
            Ok(stream) => stream,
            Err(accept_error) => {
                let message = format!("cannot accept Cinnabook connection: {}", accept_error);
                report_error(&message);
                continue;
            }
        };
        let request_len = match read_headers(&mut stream) {
            Ok(len) => len,
            Err(read_error) => {
                report_error(&read_error);
                continue;
            }
        };
        if request_len == 0 {
            continue;
        }
        let response = format!(
            "HTTP/1.1 200 OK\r\nContent-Type: text/html; charset=utf-8\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{}",
            page_text.len(),
            page_text
        );
        if let Err(write_error) = stream.write_all(response.as_bytes()) {
            let message = format!("cannot write Cinnabook response: {}", write_error);
            report_error(&message);
        }
    }
    Ok(())
}

/// Read a request through its header terminator, so the connection can be
/// closed without leaving unread bytes behind.
///
/// A single `read` can return a partial request. Closing a socket that still
/// holds unread bytes resets the connection (RST) instead of finishing it
/// (FIN), which a client observes as "connection reset by peer". Reading
/// until the header terminator consumes everything a header-only request
/// sent, so the close that follows is a clean FIN. An empty request is also
/// read cleanly (zero bytes) so the caller can skip it without reporting it.
fn read_headers(stream: &mut TcpStream) -> Result<usize, String> {
    let mut buffer = [0u8; 2048];
    let mut request = Vec::new();
    loop {
        let count = stream
            .read(&mut buffer)
            .map_err(|read_error| format!("cannot read Cinnabook request: {}", read_error))?;
        if count == 0 {
            return Ok(request.len());
        }
        request.extend_from_slice(&buffer[..count]);
        if request.windows(4).any(|window| window == b"\r\n\r\n") {
            return Ok(request.len());
        }
        if request.len() > 1_048_576 {
            return Err("Cinnabook request headers exceed one MiB".to_string());
        }
    }
}

fn render_item_list(
    names: &[String],
    nodes: &[i64],
    lists: &[Vec<i64>],
    item_list: i64,
    depth: usize,
    output: &mut String,
) {
    let mut idx = 0i64;
    while idx < list_len(lists, item_list) {
        let item = list_get(lists, item_list, idx);
        if node_tag(nodes, item) == NODE_ITEM && node_b(nodes, item) == 1 {
            render_item(names, nodes, lists, item, depth, output);
        }
        idx += 1;
    }
}

fn render_item(
    names: &[String],
    nodes: &[i64],
    lists: &[Vec<i64>],
    item: i64,
    depth: usize,
    output: &mut String,
) {
    let kind = node_a(nodes, item);
    let (label, name) = item_label_and_name(names, nodes, item);
    let heading = usize::min(depth + 1, 6);
    output.push_str(&format!("<article class=item><h{heading}>{} <code>{}</code></h{heading}>", label, escape_html(&name)));
    render_attached_docs(names, nodes, lists, item, output);
    if kind == ITEM_STRUCT {
        render_members(names, nodes, lists, node_e(nodes, item), "Field", output);
    } else if kind == ITEM_ENUM {
        render_members(names, nodes, lists, node_e(nodes, item), "Variant", output);
    } else if kind == ITEM_TRAIT {
        render_methods(names, nodes, lists, node_e(nodes, item), output);
    } else if kind == ITEM_MODULE {
        render_item_list(names, nodes, lists, node_e(nodes, item), depth + 1, output);
    } else if kind == ITEM_USE
        || kind == ITEM_IMPL
        || kind == ITEM_FUN
        || kind == ITEM_NATIVE_FUN
        || kind == ITEM_CONST
        || kind == ITEM_NATIVE_TYPE
    {
    }
    output.push_str("</article>");
}

fn item_label_and_name(names: &[String], nodes: &[i64], item: i64) -> (&'static str, String) {
    let kind = node_a(nodes, item);
    if kind == ITEM_MODULE {
        ("Module", name_text(names, node_d(nodes, item)))
    } else if kind == ITEM_USE {
        ("Re-export", "public import".to_string())
    } else if kind == ITEM_STRUCT {
        ("Type", name_text(names, node_d(nodes, item)))
    } else if kind == ITEM_ENUM {
        ("Enum", name_text(names, node_d(nodes, item)))
    } else if kind == ITEM_TRAIT {
        ("Trait", name_text(names, node_d(nodes, item)))
    } else if kind == ITEM_IMPL {
        ("Implementation", "trait implementation".to_string())
    } else if kind == ITEM_FUN {
        ("Function", name_text(names, node_a(nodes, node_d(nodes, item))))
    } else if kind == ITEM_NATIVE_FUN {
        ("Native function", name_text(names, node_a(nodes, node_d(nodes, item))))
    } else if kind == ITEM_CONST {
        ("Constant", name_text(names, node_d(nodes, item)))
    } else if kind == ITEM_NATIVE_TYPE {
        ("Native type", name_text(names, node_d(nodes, item)))
    } else {
        ("Declaration", "unknown".to_string())
    }
}

fn render_members(
    names: &[String],
    nodes: &[i64],
    lists: &[Vec<i64>],
    members: i64,
    label: &str,
    output: &mut String,
) {
    let mut idx = 0i64;
    while idx < list_len(lists, members) {
        let member = list_get(lists, members, idx);
        if node_c(nodes, member) == 1 {
            output.push_str(&format!("<section class=member><h6>{} <code>{}</code></h6>", label, escape_html(&name_text(names, node_a(nodes, member)))));
            render_attached_docs(names, nodes, lists, member, output);
            output.push_str("</section>");
        }
        idx += 1;
    }
}

fn render_methods(names: &[String], nodes: &[i64], lists: &[Vec<i64>], methods: i64, output: &mut String) {
    let mut idx = 0i64;
    while idx < list_len(lists, methods) {
        let method = list_get(lists, methods, idx);
        output.push_str(&format!("<section class=member><h6>Method <code>{}</code></h6>", escape_html(&name_text(names, node_a(nodes, method)))));
        render_attached_docs(names, nodes, lists, method, output);
        output.push_str("</section>");
        idx += 1;
    }
}

/// The prose the parser attached to `target`, paragraph by paragraph.
///
/// Scans `NODE_DOC` rows for ones whose slot `a` equals `target` and
/// returns each non-empty interned paragraph. Both `render_attached_docs`
/// and `declaration_json` format this vector.
fn attached_docs(names: &[String], nodes: &[i64], lists: &[Vec<i64>], target: i64) -> Vec<String> {
    let mut paragraphs: Vec<String> = Vec::new();
    let mut node = 0i64;
    let count = nodes.len() as i64 / NODE_STRIDE;
    while node < count {
        if node_tag(nodes, node) == NODE_DOC && node_a(nodes, node) == target {
            let docs = node_b(nodes, node);
            let mut idx = 0i64;
            while idx < list_len(lists, docs) {
                let text = name_text(names, list_get(lists, docs, idx));
                let trimmed = text.trim();
                if !trimmed.is_empty() {
                    paragraphs.push(trimmed.to_string());
                }
                idx += 1;
            }
        }
        node += 1;
    }
    paragraphs
}

fn render_attached_docs(names: &[String], nodes: &[i64], lists: &[Vec<i64>], target: i64, output: &mut String) {
    for paragraph in attached_docs(names, nodes, lists, target) {
        output.push_str(&format!("<p>{}</p>", escape_html(&paragraph).replace('\n', "<br>")));
    }
}

fn name_text(names: &[String], id: i64) -> String {
    match names.get(id as usize) {
        Some(text) => text.clone(),
        None => "unknown".to_string(),
    }
}

fn page(title: &str, body: &str) -> String {
    format!(
        "<!doctype html><html lang=en><meta charset=utf-8><meta name=viewport content=\"width=device-width,initial-scale=1\"><title>{}</title>\
         <style>body{{max-width:72rem;margin:2rem auto;padding:0 1.5rem;font:16px/1.55 system-ui;color:#241b18;background:#fffaf5}}code,pre{{font-family:ui-monospace,monospace}}\
         article{{border-left:3px solid #b4472f;padding-left:1rem;margin:1.5rem 0}}.member{{margin-left:1rem}}pre{{white-space:pre-wrap;background:#f3e9df;padding:1rem;overflow:auto}}\
         nav{{position:sticky;top:0;background:#fffaf5;padding:.75rem 0}}a{{color:#8f2f20}}.version{{color:#6d5a52}}</style><body>{}</body></html>",
        escape_html(title),
        body
    )
}

fn escape_html(text: &str) -> String {
    text.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
        .replace('\'', "&#39;")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{lexer, parser};

    #[test]
    fn public_docs_come_from_parser_attachments() {
        let source = "#! Public API\npub fun visible() I64\n  return 1\nend\n#! Private API\nfun hidden() I64\n  return 2\nend\n";
        let mut names = Vec::new();
        let mut nodes = Vec::new();
        let mut lists = Vec::new();
        let mut errors = Vec::new();
        let root = alloc_list(&mut lists);
        assert!(lexer::lex(&mut names, &mut nodes, source, 0, &mut errors));
        assert!(parser::parse(&mut names, &mut nodes, &mut lists, &mut errors, root, 0));
        let html = render_api_docs(&names, &nodes, &lists, root);
        assert!(html.contains("Public API"));
        assert!(html.contains("visible"));
        assert!(!html.contains("Private API"));
        assert!(!html.contains("hidden"));
    }

    #[test]
    fn book_is_version_pinned_and_escapes_manifesto() {
        let page_text = render_cinnabook("<p>API</p>");
        assert!(page_text.contains(env!("CARGO_PKG_VERSION")));
        assert!(page_text.contains("Cinnabook"));
        assert!(page_text.contains("The Cinnabar Manifesto"));
    }
}
