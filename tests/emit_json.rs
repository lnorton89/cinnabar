//! The `--emit-json` document surfaces, driven through the built binary.
//!
//! Every one of these runs the real compiler and parses what it wrote, so a
//! flag that parses but reaches no emitter, or a document whose shape has
//! drifted from what a consumer was promised, fails here. The documents are
//! checked against the human rendering of the same run wherever both exist:
//! the point of the JSON surface is to say the same thing in another
//! spelling, and a test that only read the JSON could not notice it had
//! stopped doing that.
//!
//! **Invariants:**
//! - No test asserts a span it did not read out of the source text. A
//!   diagnostic that pointed somewhere plausible but wrong would satisfy a
//!   test that only checked the field was present.
//! - Scratch directories are unique per process and per invocation.

use serde_json::Value;
use std::error::Error;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::{SystemTime, UNIX_EPOCH};

fn fixture(rel: &str) -> String {
    format!("{}/tests/fixtures/{}", env!("CARGO_MANIFEST_DIR"), rel)
}

fn unique_directory(label: &str) -> PathBuf {
    let nanos = match SystemTime::now().duration_since(UNIX_EPOCH) {
        Ok(duration) => duration.as_nanos(),
        Err(time_error) => time_error.duration().as_nanos(),
    };
    std::env::temp_dir().join(format!("cinnabar_{}_{}_{}", label, std::process::id(), nanos))
}

fn path_text(path: &Path) -> String {
    path.to_string_lossy().to_string()
}

fn run(arguments: &[&str]) -> Result<Output, Box<dyn Error>> {
    Ok(Command::new(env!("CARGO_BIN_EXE_cinnabar")).args(arguments).output()?)
}

fn document(arguments: &[&str]) -> Result<(Value, bool), Box<dyn Error>> {
    let output = run(arguments)?;
    let parsed: Value = serde_json::from_slice(&output.stdout)?;
    Ok((parsed, output.status.success()))
}

fn format_of(report: &Value) -> String {
    report.get("format").and_then(Value::as_str).unwrap_or_default().to_string()
}

fn array_of<'a>(report: &'a Value, key: &str) -> Result<&'a Vec<Value>, Box<dyn Error>> {
    report
        .get(key)
        .and_then(Value::as_array)
        .ok_or_else(|| format!("report had no '{}' array: {}", key, report).into())
}

const STRUCT_SOURCE: &str = "pub type Pair\n  pub left: I64\n  pub right: I64\nend\n\nfun main() I32\n  val pair = Pair(left: 1, right: 2)\n  if pair.left == 1\n  return 0\n  else\n  return 1\n  end\nend\n";

#[test]
fn parse_only_arena_is_emitted_as_a_document() -> Result<(), Box<dyn Error>> {
    let (report, accepted) = document(&[&fixture("spec.cnb"), "--dump-ast", "--emit-json"])?;
    assert!(accepted, "parse-only dump should succeed on the reference fixture");
    assert_eq!(format_of(&report), "cinnabar.ast.v1");

    let nodes = array_of(&report, "nodes")?;
    assert!(!nodes.is_empty(), "arena document carried no nodes");
    let names = array_of(&report, "names")?;
    assert!(!names.is_empty(), "arena document carried no interning table");
    array_of(&report, "lists")?;

    // The root is an index into the list arena, and following it has to
    // land on real item rows: that is the only thing that makes the flat
    // arena walkable by a consumer.
    let root = report.get("root").and_then(Value::as_i64).ok_or("document had no root")?;
    let lists = array_of(&report, "lists")?;
    let root_items = lists
        .get(root as usize)
        .and_then(Value::as_array)
        .ok_or("root did not name a list in the list arena")?;
    assert!(!root_items.is_empty(), "root item list was empty");
    for entry in root_items {
        let id = entry.as_i64().ok_or("root list held a non-integer")?;
        let node = nodes.get(id as usize).ok_or("root list referenced a node outside the arena")?;
        assert_eq!(node.get("tag").and_then(Value::as_str), Some("ITEM"));
    }

    // Parsing alone attaches no types, so no expression may claim one yet.
    let typed = nodes.iter().any(|node| {
        node.get("tag").and_then(Value::as_str) == Some("EXPR")
            && node.get("detail").and_then(|detail| detail.get("ty")).is_some()
    });
    assert!(!typed, "the parse-only arena carried a type attachment");
    Ok(())
}

#[test]
fn the_typed_arena_document_carries_the_attached_facts() -> Result<(), Box<dyn Error>> {
    let entry = fixture("spec.cnb");
    let (report, accepted) = document(&[&entry, "--dump-typed-ast", "--emit-json"])?;
    assert!(accepted, "typed dump should succeed on the reference fixture");
    assert_eq!(format_of(&report), "cinnabar.typed-ast.v1");
    let nodes = array_of(&report, "nodes")?;

    let typed_expressions = nodes
        .iter()
        .filter(|node| node.get("tag").and_then(Value::as_str) == Some("EXPR"))
        .filter(|node| node.get("detail").and_then(|detail| detail.get("ty")).is_some())
        .count();
    assert!(typed_expressions > 0, "no expression carried the typechecker's attached type");

    let resolved_symbols = nodes
        .iter()
        .filter(|node| node.get("tag").and_then(Value::as_str) == Some("SYM"))
        .count();
    assert!(resolved_symbols > 0, "no resolver symbol rows reached the document");

    // Every rendered type comes with the canonical key it was rendered
    // from, so a consumer can group two spellings of one type.
    for node in nodes {
        if let Some(ty) = node.get("detail").and_then(|detail| detail.get("ty")) {
            assert!(ty.get("key").and_then(Value::as_i64).is_some(), "type attachment without a key: {}", node);
            assert!(ty.get("rendered").and_then(Value::as_str).is_some(), "type attachment without a rendering: {}", node);
        }
    }
    Ok(())
}

#[test]
fn a_descriptor_row_reports_no_source_because_it_has_none() -> Result<(), Box<dyn Error>> {
    let (report, accepted) = document(&[&fixture("spec.cnb"), "--dump-typed-ast", "--emit-json"])?;
    assert!(accepted);
    let nodes = array_of(&report, "nodes")?;
    let descriptors: Vec<&Value> = nodes
        .iter()
        .filter(|node| node.get("tag").and_then(Value::as_str) == Some("TYINFO"))
        .collect();
    assert!(!descriptors.is_empty(), "the reference fixture produced no type descriptors");
    // TYINFO rows hold linearity flags in the file and start slots, so
    // `source` must be null on every one of them.
    for descriptor in &descriptors {
        assert_eq!(descriptor.get("source"), Some(&Value::Null), "descriptor row claimed a source: {}", descriptor);
        let detail = descriptor.get("detail").ok_or("descriptor row had no detail")?;
        assert!(detail.get("linear").and_then(Value::as_i64).is_some(), "descriptor lost its linearity flag");
        assert!(detail.get("descriptor").and_then(Value::as_str).is_some(), "descriptor lost its kind");
    }

    // Every other row's source, where it has one, agrees with the raw slots
    // it was rendered from.
    for node in nodes {
        if let Some(source) = node.get("source").filter(|value| !value.is_null()) {
            assert_eq!(source.get("file_id").and_then(Value::as_i64), node.get("file").and_then(Value::as_i64));
            assert_eq!(source.get("start").and_then(Value::as_i64), node.get("start").and_then(Value::as_i64));
            assert_eq!(source.get("end").and_then(Value::as_i64), node.get("end").and_then(Value::as_i64));
        }
    }
    Ok(())
}

#[test]
fn the_layout_document_reports_the_same_numbers_as_the_text_report() -> Result<(), Box<dyn Error>> {
    let directory = unique_directory("emit_json_layout");
    std::fs::create_dir_all(&directory)?;
    let source = directory.join("main.cnb");
    std::fs::write(&source, STRUCT_SOURCE)?;
    let entry = path_text(&source);

    let text_report = run(&[&entry, "--print-layout"])?;
    assert!(text_report.status.success(), "text layout report failed");
    let text = String::from_utf8_lossy(&text_report.stdout).to_string();

    let (report, accepted) = document(&[&entry, "--print-layout", "--emit-json"])?;
    assert!(accepted, "layout document failed");
    assert_eq!(format_of(&report), "cinnabar.layout.v1");
    let target = report.get("target").and_then(Value::as_str).ok_or("layout document named no target")?;
    assert!(text.contains(target), "the two reports disagree about the target: {}", text);

    let types = array_of(&report, "types")?;
    let pair = types
        .iter()
        .find(|entry| entry.get("type").and_then(Value::as_str) == Some("Pair"))
        .ok_or("layout document omitted the declared struct")?;
    assert_eq!(pair.get("kind").and_then(Value::as_str), Some("struct"));
    let size = pair.get("size").and_then(Value::as_u64).ok_or("struct had no size")?;
    let align = pair.get("align").and_then(Value::as_u64).ok_or("struct had no alignment")?;
    // Two I64 fields laid out end to end: the document must say so, and so
    // must the text report it is a second rendering of.
    assert_eq!(size, 16);
    assert_eq!(align, 8);
    assert!(
        text.contains(&format!("struct Pair  size={} align={}", size, align)),
        "text report disagreed with the document: {}",
        text
    );
    let fields = array_of(pair, "fields")?;
    assert_eq!(fields.len(), 2);
    let offsets: Vec<i64> = fields.iter().filter_map(|field| field.get("offset").and_then(Value::as_i64)).collect();
    assert_eq!(offsets, vec![0, 8]);

    std::fs::remove_dir_all(&directory)?;
    Ok(())
}

#[test]
fn a_rejected_program_emits_the_diagnostic_envelope() -> Result<(), Box<dyn Error>> {
    let entry = fixture("unknown_var.cnb");
    let source = std::fs::read_to_string(&entry)?;
    let (report, accepted) = document(&[&entry, "--emit-json"])?;
    assert!(!accepted, "an invalid program reported success");
    assert_eq!(format_of(&report), "cinnabar.diagnostics.v1");

    let diagnostics = array_of(&report, "diagnostics")?;
    assert!(!diagnostics.is_empty(), "a rejected program produced no diagnostics");
    let first = diagnostics.first().ok_or("diagnostics array was empty")?;
    assert_eq!(first.get("severity").and_then(Value::as_str), Some("error"));

    // Slice the source with the reported offsets and require the message
    // to contain what they select.
    let span = first.get("source").ok_or("diagnostic carried no source")?;
    let start = span.get("start").and_then(Value::as_i64).ok_or("source had no start")? as usize;
    let end = span.get("end").and_then(Value::as_i64).ok_or("source had no end")? as usize;
    let selected = source.get(start..end).ok_or("diagnostic span fell outside the source")?;
    let message = first.get("message").and_then(Value::as_str).unwrap_or_default();
    assert!(message.contains(selected), "message {:?} does not name what its span selects ({:?})", message, selected);

    // Line and column are derived from the same offsets and must agree
    // with them.
    let line = span.get("start_line").and_then(Value::as_i64).ok_or("source had no line")?;
    let column = span.get("start_column").and_then(Value::as_i64).ok_or("source had no column")?;
    let prefix = source.get(..start).ok_or("start fell outside the source")?;
    assert_eq!(line, prefix.matches('\n').count() as i64, "reported line disagrees with the offset");
    let line_start = match prefix.rfind('\n') {
        Some(position) => position + 1,
        None => 0,
    };
    let column_text = source.get(line_start..start).unwrap_or_default();
    assert_eq!(column, column_text.encode_utf16().count() as i64, "reported column disagrees with the offset");
    Ok(())
}

#[test]
fn borrow_explanations_ride_the_same_envelope_under_either_spelling() -> Result<(), Box<dyn Error>> {
    let entry = fixture("explain_leak.cnb");
    let (from_flag, flag_accepted) = document(&[&entry, "--explain-borrow=json"])?;
    let (from_emit, emit_accepted) = document(&[&entry, "--emit-json"])?;
    assert!(!flag_accepted && !emit_accepted, "borrow-invalid input unexpectedly succeeded");
    assert_eq!(format_of(&from_flag), "cinnabar.diagnostics.v1");
    assert_eq!(
        from_flag, from_emit,
        "--explain-borrow=json and --emit-json disagreed about the same program"
    );

    let diagnostics = array_of(&from_emit, "diagnostics")?;
    let explained = diagnostics.iter().any(|diagnostic| {
        diagnostic
            .get("explanations")
            .and_then(Value::as_array)
            .is_some_and(|explanations| explanations.len() >= 2)
    });
    assert!(explained, "the envelope omitted the checker's consume paths: {}", from_emit);

    // Every explanation points into the file it is explaining. The notes
    // exist to name a binding site or a path exit, and one without a real
    // location would be worse than none.
    for diagnostic in diagnostics {
        let explanations = array_of(diagnostic, "explanations")?;
        for explanation in explanations {
            let path = explanation
                .get("source")
                .and_then(|source| source.get("path"))
                .and_then(Value::as_str)
                .ok_or("an explanation carried no source path")?;
            assert!(path.ends_with("explain_leak.cnb"), "explanation pointed at {}", path);
        }
    }
    Ok(())
}

#[test]
fn an_accepted_program_still_emits_exactly_one_document() -> Result<(), Box<dyn Error>> {
    let directory = unique_directory("emit_json_accepted");
    std::fs::create_dir_all(&directory)?;
    let source = directory.join("main.cnb");
    std::fs::write(&source, STRUCT_SOURCE)?;
    let entry = path_text(&source);

    // A consumer parses one document per invocation whatever the verdict
    // was, rather than having to recognize a success sentence as "not an
    // error".
    let (checked, check_accepted) = document(&[&entry, "--check-only", "--emit-json"])?;
    assert!(check_accepted, "a valid program failed the front end");
    assert_eq!(format_of(&checked), "cinnabar.diagnostics.v1");
    assert!(array_of(&checked, "diagnostics")?.is_empty(), "a clean run reported diagnostics");

    let emitted = directory.join("main.ll");
    let (built, build_accepted) = document(&[&entry, "--emit-llvm", "-o", &path_text(&emitted), "--emit-json"])?;
    assert!(build_accepted, "a valid program failed to emit IR");
    assert!(array_of(&built, "diagnostics")?.is_empty());
    assert!(std::fs::read_to_string(&emitted)?.contains("define"), "IR was not written alongside the document");

    std::fs::remove_dir_all(&directory)?;
    Ok(())
}

#[test]
fn json_and_human_renderings_report_the_same_verdict() -> Result<(), Box<dyn Error>> {
    // The exit status must match between the two renderings for every
    // fixture.
    let cases = [
        ("spec.cnb", true),
        ("unknown_var.cnb", false),
        ("invalid_casing.cnb", false),
        ("immutable_assign.cnb", false),
        ("explain_leak.cnb", false),
    ];
    for (name, expected) in cases {
        let entry = fixture(name);
        let human = run(&[&entry, "--check-only"])?;
        let json = run(&[&entry, "--check-only", "--emit-json"])?;
        assert_eq!(human.status.success(), expected, "{}: unexpected human verdict", name);
        assert_eq!(json.status.success(), expected, "{}: unexpected JSON verdict", name);
        serde_json::from_slice::<Value>(&json.stdout)
            .map_err(|parse_error| format!("{}: stdout was not one JSON document: {}", name, parse_error))?;
    }
    Ok(())
}
