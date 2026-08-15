//! The loopback HTTP server and page behind `cinnabar snapshots`.
//!
//! Reads `project::snapshot_report`, which recompiles every rejection test
//! and returns a `SnapshotEntry` per fixture holding the normalized sidecar
//! contents and the normalized diagnostic the compiler emits now. Serves
//! that as `cinnabar.snapshots.v1` on `GET /api/snapshots`, writes one
//! sidecar through `project::accept_snapshot` on `POST /api/accept`, and
//! serves the inlined review page on `GET /`.
//!
//! The page computes a line-level longest-common-subsequence diff of the
//! two strings in the browser and posts back the `actual` string it was
//! given, so an accepted sidecar holds exactly the bytes
//! `--update-snapshots` would have written.
//!
//! **Invariants:**
//! - The bind address must be loopback; a non-loopback address is rejected
//!   before the listener is created.
//! - Request bodies above `MAX_BODY_BYTES` are rejected without being
//!   buffered further.
//! - Sidecar writes go through `project::accept_snapshot`, which applies
//!   the same root-confinement check as every other sidecar write.

use crate::project::{accept_snapshot, snapshot_report, ManifestError, ProjectManifest};
use serde_json::{json, Value};
use std::io::{Read, Write};
use std::net::{SocketAddr, TcpListener, TcpStream};
use std::path::Path;

/// The document `GET /api/snapshots` answers with.
pub const SNAPSHOTS_FORMAT: &str = "cinnabar.snapshots.v1";

/// Largest request body buffered, in bytes. Reading stops and the request
/// is rejected once the accumulated body exceeds this.
const MAX_BODY_BYTES: usize = 1024 * 1024;

/// Build the report as a JSON document.
pub fn snapshots_json(executable: &Path, manifest: &ProjectManifest) -> Result<Value, ManifestError> {
    let entries = snapshot_report(executable, manifest)?;
    let mut rows: Vec<Value> = Vec::new();
    let mut idx = 0usize;
    while idx < entries.len() {
        match entries.get(idx) {
            Some(entry) => rows.push(json!({
                "test": entry.test,
                "snapshot": entry.snapshot,
                "recorded": entry.recorded,
                "expected": entry.expected,
                "actual": entry.actual,
                "rejected": entry.rejected,
                "agrees": entry.agrees()
            })),
            None => break,
        }
        idx += 1;
    }
    Ok(json!({
        "format": SNAPSHOTS_FORMAT,
        "root": manifest.root.to_string_lossy(),
        "snapshots": rows
    }))
}

/// Serve the review page and its two endpoints until interrupted.
pub fn serve(
    address: &str,
    executable: &Path,
    manifest: &ProjectManifest,
    mut report_error: impl FnMut(&str),
) -> Result<(), String> {
    let parsed: SocketAddr = address
        .parse()
        .map_err(|parse_error| format!("invalid snapshot review address: {}", parse_error))?;
    if !parsed.ip().is_loopback() {
        return Err("the snapshot reviewer may bind only to a loopback address".to_string());
    }
    let listener = TcpListener::bind(parsed)
        .map_err(|bind_error| format!("cannot bind snapshot reviewer: {}", bind_error))?;
    // As with the other servers here, only the bind is fatal: one visitor's
    // broken connection must not end the session for the reviewer.
    for incoming in listener.incoming() {
        let mut stream = match incoming {
            Ok(stream) => stream,
            Err(accept_error) => {
                report_error(&format!("cannot accept snapshot review connection: {}", accept_error));
                continue;
            }
        };
        if let Err(request_error) = handle(&mut stream, executable, manifest) {
            let written = respond(&mut stream, "400 Bad Request", "text/plain; charset=utf-8", request_error.as_bytes());
            if let Err(write_error) = written {
                report_error(&format!("cannot write snapshot review error: {}", write_error));
            }
        }
    }
    Ok(())
}

fn handle(stream: &mut TcpStream, executable: &Path, manifest: &ProjectManifest) -> Result<(), String> {
    let (headers, body) = read_request(stream)?;
    if headers.starts_with("GET / ") {
        return respond(stream, "200 OK", "text/html; charset=utf-8", PAGE.as_bytes());
    }
    if headers.starts_with("GET /api/snapshots ") {
        let report = snapshots_json(executable, manifest).map_err(|failure| failure.message())?;
        let text = serde_json::to_string(&report)
            .map_err(|serialize_error| format!("cannot serialize snapshot report: {}", serialize_error))?;
        return respond(stream, "200 OK", "application/json; charset=utf-8", text.as_bytes());
    }
    if headers.starts_with("POST /api/accept ") {
        let request: Value = serde_json::from_slice(&body)
            .map_err(|parse_error| format!("accept request is not JSON: {}", parse_error))?;
        let snapshot = request
            .get("snapshot")
            .and_then(Value::as_str)
            .ok_or_else(|| "accept request names no snapshot".to_string())?;
        let text = request
            .get("text")
            .and_then(Value::as_str)
            .ok_or_else(|| "accept request carries no text".to_string())?;
        accept_snapshot(manifest, snapshot, text).map_err(|failure| failure.message())?;
        let answer = json!({ "accepted": snapshot });
        let rendered = serde_json::to_string(&answer)
            .map_err(|serialize_error| format!("cannot serialize acceptance: {}", serialize_error))?;
        return respond(stream, "200 OK", "application/json; charset=utf-8", rendered.as_bytes());
    }
    respond(stream, "404 Not Found", "text/plain; charset=utf-8", b"not found")
}

fn read_request(stream: &mut TcpStream) -> Result<(String, Vec<u8>), String> {
    let mut buffer: Vec<u8> = Vec::new();
    let mut chunk = [0u8; 4096];
    loop {
        let read = stream
            .read(&mut chunk)
            .map_err(|read_error| format!("cannot read snapshot review request: {}", read_error))?;
        if read == 0 {
            break;
        }
        match chunk.get(..read) {
            Some(slice) => buffer.extend_from_slice(slice),
            None => break,
        }
        if buffer.len() > MAX_BODY_BYTES {
            return Err("snapshot review request is too large".to_string());
        }
        let text = String::from_utf8_lossy(&buffer).to_string();
        if let Some(split) = text.find("\r\n\r\n") {
            let head = text.get(..split).unwrap_or_default().to_string();
            let content_length = content_length_of(&head);
            let body_start = split + 4;
            if buffer.len() >= body_start + content_length {
                let body = buffer.get(body_start..body_start + content_length).unwrap_or_default().to_vec();
                return Ok((head, body));
            }
        }
    }
    let text = String::from_utf8_lossy(&buffer).to_string();
    Ok((text, Vec::new()))
}

fn content_length_of(head: &str) -> usize {
    for line in head.lines() {
        let lowered = line.to_ascii_lowercase();
        if let Some(value) = lowered.strip_prefix("content-length:") {
            return value.trim().parse::<usize>().unwrap_or(0);
        }
    }
    0
}

fn respond(stream: &mut TcpStream, status: &str, content_type: &str, body: &[u8]) -> Result<(), String> {
    let head = format!(
        "HTTP/1.1 {}\r\nContent-Type: {}\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
        status,
        content_type,
        body.len()
    );
    stream
        .write_all(head.as_bytes())
        .and_then(|()| stream.write_all(body))
        .map_err(|write_error| format!("cannot write snapshot review response: {}", write_error))
}

// The page. Inlined rather than served from disk so the reviewer works from
// an installed binary with no asset directory beside it, and so a diff of
// what it shows is a diff of this file.
const PAGE: &str = r#"<!doctype html>
<html lang=en>
<meta charset=utf-8>
<meta name=viewport content="width=device-width,initial-scale=1">
<title>Cinnabar snapshot review</title>
<style>
:root{color-scheme:light dark;--bg:#fffaf5;--raised:#f4ece4;--border:#ddd0c4;--text:#241b18;--dim:#6b5b52;--add:#1a7f37;--del:#b32d2e;--accent:#b7410e;--mono:ui-monospace,SFMono-Regular,Menlo,Consolas,monospace}
@media(prefers-color-scheme:dark){:root{--bg:#1a1614;--raised:#241d1a;--border:#3a2f2a;--text:#f0e7e0;--dim:#a8968c;--add:#56d364;--del:#ff7b72;--accent:#e8643a}}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--text);font:15px/1.55 system-ui,-apple-system,"Segoe UI",sans-serif}
header{padding:20px 24px 14px;border-bottom:1px solid var(--border)}
h1{margin:0 0 4px;font-size:19px}
header p{margin:0;color:var(--dim)}
main{padding:16px 24px 60px;max-width:1100px}
.summary{margin:0 0 18px;color:var(--dim)}
.entry{border:1px solid var(--border);border-radius:8px;margin-bottom:16px;overflow:hidden}
.entry__head{display:flex;gap:12px;align-items:baseline;justify-content:space-between;padding:10px 14px;background:var(--raised)}
.entry__name{font-family:var(--mono);font-size:13px}
.entry__state{font-size:12px;text-transform:uppercase;letter-spacing:.08em}
.state--agrees{color:var(--add)}
.state--differs{color:var(--del)}
.state--new{color:var(--accent)}
.state--accepted{color:var(--add)}
.diff{margin:0;padding:10px 14px;font-family:var(--mono);font-size:12.5px;white-space:pre-wrap;word-break:break-word}
.diff div{padding:0 4px;border-radius:3px}
.diff .del{background:color-mix(in srgb,var(--del) 16%,transparent);color:var(--del)}
.diff .add{background:color-mix(in srgb,var(--add) 16%,transparent);color:var(--add)}
.actions{display:flex;gap:8px;padding:0 14px 12px}
button{font:inherit;padding:6px 14px;border-radius:6px;border:1px solid var(--border);background:var(--bg);color:var(--text);cursor:pointer}
button.accept{background:var(--accent);border-color:var(--accent);color:#fff}
button:disabled{opacity:.5;cursor:default}
.empty{color:var(--dim)}
.error{color:var(--del)}
details summary{cursor:pointer;color:var(--dim);padding:0 14px 12px}
</style>
<header>
  <h1>Snapshot review</h1>
  <p>Every rejection test, with the diagnostic its <code>.stderr</code> sidecar records and the one the compiler prints now. Accepting writes that one sidecar and nothing else.</p>
</header>
<main id=app><p class=empty>Loading…</p></main>
<script>
const app = document.getElementById("app");

// A line-level longest-common-subsequence diff. Enough to read a reworded
// diagnostic, which is what these snapshots hold; nothing here needs to be
// a general-purpose diff tool.
function diffLines(before, after) {
  const a = before === "" ? [] : before.split("\n");
  const b = after === "" ? [] : after.split("\n");
  const table = Array.from({ length: a.length + 1 }, () => new Array(b.length + 1).fill(0));
  for (let i = a.length - 1; i >= 0; i--) {
    for (let j = b.length - 1; j >= 0; j--) {
      table[i][j] = a[i] === b[j] ? table[i + 1][j + 1] + 1 : Math.max(table[i + 1][j], table[i][j + 1]);
    }
  }
  const rows = [];
  let i = 0, j = 0;
  while (i < a.length && j < b.length) {
    if (a[i] === b[j]) { rows.push(["same", a[i]]); i++; j++; }
    else if (table[i + 1][j] >= table[i][j + 1]) { rows.push(["del", a[i]]); i++; }
    else { rows.push(["add", b[j]]); j++; }
  }
  while (i < a.length) { rows.push(["del", a[i++]]); }
  while (j < b.length) { rows.push(["add", b[j++]]); }
  return rows;
}

function escape(text) {
  return text.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
}

function stateOf(entry) {
  if (entry.agrees) return ["agrees", "unchanged"];
  if (!entry.recorded) return ["new", "no snapshot recorded"];
  return ["differs", "differs"];
}

function render(report) {
  const entries = report.snapshots;
  const differing = entries.filter((entry) => !entry.agrees);
  const parts = [];
  parts.push(`<p class=summary>${entries.length} rejection test${entries.length === 1 ? "" : "s"} in <code>${escape(report.root)}</code>; ${differing.length} to review.</p>`);
  if (entries.length === 0) {
    parts.push("<p class=empty>This project has no rejection tests.</p>");
  }
  for (const entry of entries) {
    const [tone, label] = stateOf(entry);
    const rows = diffLines(entry.expected, entry.actual)
      .map(([kind, line]) => `<div class="${kind}">${kind === "del" ? "-" : kind === "add" ? "+" : " "} ${escape(line)}</div>`)
      .join("");
    const warning = entry.rejected ? "" : `<p class=error style="padding:0 14px">The compiler no longer rejects this program. A snapshot cannot fix that — the test itself is now wrong.</p>`;
    const body = entry.agrees
      ? `<details><summary>Unchanged — show the recorded diagnostic</summary><pre class=diff>${escape(entry.expected)}</pre></details>`
      : `<pre class=diff>${rows}</pre>${warning}<div class=actions>
           <button class=accept data-snapshot="${escape(entry.snapshot)}">Accept this diagnostic</button>
           <button data-skip>Leave it</button>
         </div>`;
    parts.push(`<section class=entry data-entry>
        <div class=entry__head>
          <span class=entry__name>${escape(entry.test)}</span>
          <span class="entry__state state--${tone}">${label}</span>
        </div>${body}</section>`);
  }
  app.innerHTML = parts.join("");

  for (const button of app.querySelectorAll("button.accept")) {
    button.addEventListener("click", async () => {
      const entry = entries.find((candidate) => candidate.snapshot === button.dataset.snapshot);
      button.disabled = true;
      try {
        const response = await fetch("/api/accept", {
          method: "POST",
          body: JSON.stringify({ snapshot: entry.snapshot, text: entry.actual }),
        });
        if (!response.ok) throw new Error(await response.text());
        const section = button.closest("[data-entry]");
        section.querySelector(".entry__state").className = "entry__state state--accepted";
        section.querySelector(".entry__state").textContent = "accepted";
        section.querySelector(".actions").remove();
      } catch (failure) {
        button.disabled = false;
        button.insertAdjacentHTML("afterend", `<span class=error>${escape(failure.message)}</span>`);
      }
    });
  }
  for (const button of app.querySelectorAll("button[data-skip]")) {
    button.addEventListener("click", () => button.closest("[data-entry]").remove());
  }
}

fetch("/api/snapshots")
  .then(async (response) => {
    if (!response.ok) throw new Error(await response.text());
    return response.json();
  })
  .then(render)
  .catch((failure) => {
    app.innerHTML = `<p class=error>${escape(failure.message)}</p>`;
  });
</script>
</html>
"#;
