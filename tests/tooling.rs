//! Integration tests for the tooling layer, against the library directly.
//!
//! Covers the analysis queries the language server is built on, byte-offset
//! to position mapping, module-loader overlays for unsaved buffers, the
//! formatter, and the borrow checker's explanatory notes. These call into
//! `cinnabar::analysis` rather than through the protocol, which is what
//! makes them the right place to pin an answer's *content*; the protocol
//! behaviour around those answers is pinned in `lsp_protocol.rs`.
//!
//! **Invariants:**
//! - Every query under test consumes facts the pipeline attached. A test
//!   here that passed while the compiler disagreed would mean the tooling
//!   had grown a second implementation, which is the thing this layer
//!   exists not to have.

use cinnabar::analysis::{
    analyze, code_actions, completions, definition, document_symbols, file_id_of, folding_ranges,
    hover, inlay_hints, offset_to_position, position_to_offset, references, rename_edits,
    semantic_tokens, signature_help, workspace_symbols, SEMANTIC_TOKEN_TYPES,
};
use cinnabar::ast::NO_FILE;
use cinnabar::format::format_source;
use serde_json::Value;
use std::error::Error;
use std::path::PathBuf;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

fn fixture(rel: &str) -> String {
    format!("{}/tests/fixtures/{}", env!("CARGO_MANIFEST_DIR"), rel)
}

fn offset_of(haystack: &str, needle: &str) -> i64 {
    match haystack.find(needle) {
        Some(pos) => pos as i64,
        None => -1,
    }
}

#[test]
fn spec_analyzes_clean() {
    let analysis = analyze(&fixture("spec.cnb"), &[]);
    assert!(analysis.resolved);
    assert!(analysis.typechecked);
    let rendered: Vec<String> = analysis.errors.iter().map(|diag| diag.0.clone()).collect();
    assert!(analysis.errors.is_empty(), "unexpected errors: {:?}", rendered);
}

#[test]
fn position_mapping_roundtrips() {
    let text = "fun a() I64\n  return 1\nend\n";
    let cases = [0i64, 4, 11, 12, 14, 25];
    let mut idx = 0usize;
    while idx < cases.len() {
        let offset = match cases.get(idx) {
            Some(value) => *value,
            None => break,
        };
        let (line, col) = offset_to_position(text, offset);
        let back = position_to_offset(text, line, col);
        assert_eq!(back, offset, "roundtrip failed for offset {}", offset);
        idx += 1;
    }
    // Multi-byte characters advance UTF-16 columns correctly: 'é' is two
    // UTF-8 bytes but one UTF-16 unit.
    let unicode = "# caf\u{e9} note\nval x = 1\n";
    let after_accent = offset_of(unicode, " note");
    let (line, col) = offset_to_position(unicode, after_accent);
    assert_eq!(line, 0);
    assert_eq!(col, 6);
    assert_eq!(position_to_offset(unicode, line, col), after_accent);
}

#[test]
fn definition_crosses_module_files() {
    let entry = fixture("multi_file/main.cnb");
    let analysis = analyze(&entry, &[]);
    assert!(analysis.resolved, "errors: {:?}", analysis.errors);
    let main_text = analysis
        .files
        .first()
        .map(|pair| pair.1.clone())
        .unwrap_or_default();
    let call_at = offset_of(&main_text, "add(10");
    assert!(call_at >= 0);
    let entry_file = file_id_of(&analysis, &entry);
    assert!(entry_file >= 0);
    let (def_file, def_start, def_end) = match definition(&analysis, entry_file, call_at) {
        Some(span) => span,
        None => (NO_FILE, 0, 0),
    };
    assert_ne!(def_file, NO_FILE, "definition of 'add' not found");
    let def_path = analysis
        .files
        .get(def_file as usize)
        .map(|pair| pair.0.clone())
        .unwrap_or_default();
    assert!(def_path.ends_with("Math.cnb"), "definition in {}", def_path);
    assert!(def_end > def_start);
}

#[test]
fn hover_shows_attached_types_and_signatures() {
    let entry = fixture("multi_file/main.cnb");
    let analysis = analyze(&entry, &[]);
    let main_text = analysis
        .files
        .first()
        .map(|pair| pair.1.clone())
        .unwrap_or_default();
    let entry_file = file_id_of(&analysis, &entry);
    // Hovering the literal 10 reports its adopted type.
    let lit_at = offset_of(&main_text, "10");
    let (lit_hover, lit_span) = match hover(&analysis, entry_file, lit_at) {
        Some(found) => found,
        None => (String::new(), (NO_FILE, 0, 0)),
    };
    assert!(lit_hover.contains("I64"), "literal hover: {}", lit_hover);
    assert_ne!(lit_span.0, NO_FILE);
    // Hovering the call to add shows the resolved signature.
    let call_at = offset_of(&main_text, "add(10");
    let (call_hover, call_span) = match hover(&analysis, entry_file, call_at) {
        Some(found) => found,
        None => (String::new(), (NO_FILE, 0, 0)),
    };
    assert!(
        call_hover.contains("fun add(a: I64, b: I64) I64"),
        "call hover: {}",
        call_hover
    );
    assert_ne!(call_span.0, NO_FILE);
}

#[test]
fn references_span_the_module_graph() {
    let entry = fixture("multi_file/main.cnb");
    let analysis = analyze(&entry, &[]);
    let main_text = analysis
        .files
        .first()
        .map(|pair| pair.1.clone())
        .unwrap_or_default();
    let entry_file = file_id_of(&analysis, &entry);
    let call_at = offset_of(&main_text, "add(10");
    let refs = references(&analysis, entry_file, call_at);
    // At least the call site in main.cnb and the declaration in Math.cnb.
    assert!(refs.len() >= 2, "references: {:?}", refs);
    let mut files_seen: Vec<i64> = Vec::new();
    let mut idx = 0usize;
    while idx < refs.len() {
        match refs.get(idx) {
            Some(span) => {
                if !files_seen.contains(&span.0) {
                    files_seen.push(span.0);
                }
            }
            None => break,
        }
        idx += 1;
    }
    assert!(files_seen.len() >= 2, "references confined to one file: {:?}", refs);
}

#[test]
fn completions_offer_symbols_locals_and_keywords() {
    let entry = fixture("multi_file/main.cnb");
    let analysis = analyze(&entry, &[]);
    let main_text = analysis
        .files
        .first()
        .map(|pair| pair.1.clone())
        .unwrap_or_default();
    let entry_file = file_id_of(&analysis, &entry);
    let inside_main = offset_of(&main_text, "return add") + 4;
    let items = completions(&analysis, entry_file, inside_main);
    let labels: Vec<String> = items.iter().map(|item| item.0.clone()).collect();
    assert!(labels.iter().any(|label| label == "main"), "missing 'main' in {:?}", labels);
    assert!(labels.iter().any(|label| label == "return"), "missing keyword in {:?}", labels);
    assert!(
        labels.iter().any(|label| label.contains("add")),
        "missing 'add' in {:?}",
        labels
    );
}

#[test]
fn completions_exclude_symbols_the_resolver_hides() {
    let entry = fixture("spec.cnb");
    let analysis = analyze(&entry, &[]);
    let text = analysis
        .files
        .first()
        .map(|pair| pair.1.clone())
        .unwrap_or_default();
    let file = file_id_of(&analysis, &entry);
    let inside_main = offset_of(&text, "return reference_checks") + 7;
    let items = completions(&analysis, file, inside_main);
    let labels: Vec<String> = items.iter().map(|item| item.0.clone()).collect();
    assert!(labels.iter().any(|label| label == "gate"), "missing visible import: {:?}", labels);
    assert!(
        !labels.iter().any(|label| label == "Runtime.probe_twice"),
        "private module member leaked into completion: {:?}",
        labels
    );
    assert!(
        !labels.iter().any(|label| label == "Binary.combine_le_bytes"),
        "private helper leaked into completion: {:?}",
        labels
    );
}

#[test]
fn completions_exclude_locals_from_sibling_branches() {
    let entry = fixture("multi_file/main.cnb");
    let source = "pub fun main() I64\n  if true\n    val only_then: I64 = 1\n    return only_then\n  else\n    val only_else: I64 = 2\n    return only_else\n  end\nend\n";
    let overlay = [(entry.clone(), source.to_string())];
    let analysis = analyze(&entry, &overlay);
    assert!(analysis.errors.is_empty(), "unexpected errors: {:?}", analysis.errors);
    let file = file_id_of(&analysis, &entry);
    let in_else = offset_of(source, "return only_else") + 7;
    let items = completions(&analysis, file, in_else);
    let labels: Vec<String> = items.iter().map(|item| item.0.clone()).collect();
    assert!(labels.iter().any(|label| label == "only_else"), "missing branch local: {:?}", labels);
    assert!(
        !labels.iter().any(|label| label == "only_then"),
        "sibling-branch local leaked into completion: {:?}",
        labels
    );
}

#[test]
fn completions_follow_resolver_visibility_and_branch_scope() {
    let entry = fixture("tooling_scope.cnb");
    let analysis = analyze(&entry, &[]);
    let text = analysis
        .files
        .first()
        .map(|pair| pair.1.clone())
        .unwrap_or_default();
    let file = file_id_of(&analysis, &entry);

    let use_cursor = offset_of(&text, "use Tools.v") + "use Tools.v".len() as i64;
    let use_items = completions(&analysis, file, use_cursor);
    let use_labels: Vec<String> = use_items.iter().map(|item| item.0.clone()).collect();
    assert!(use_labels.iter().any(|label| label == "visible"), "use items: {:?}", use_labels);
    assert!(!use_labels.iter().any(|label| label == "secret"), "private member leaked: {:?}", use_labels);

    let then_cursor = offset_of(&text, "return only_then") + "return ".len() as i64;
    let then_items = completions(&analysis, file, then_cursor);
    let then_labels: Vec<String> = then_items.iter().map(|item| item.0.clone()).collect();
    assert!(then_labels.iter().any(|label| label == "only_then"), "then items: {:?}", then_labels);
    assert!(!then_labels.iter().any(|label| label == "only_else"), "else local leaked: {:?}", then_labels);
}

#[test]
fn signature_help_tracks_the_active_argument() {
    let entry = fixture("multi_file/main.cnb");
    let analysis = analyze(&entry, &[]);
    let main_text = analysis
        .files
        .first()
        .map(|pair| pair.1.clone())
        .unwrap_or_default();
    let entry_file = file_id_of(&analysis, &entry);
    let second_arg = offset_of(&main_text, "20");
    let info_found = signature_help(&analysis, entry_file, second_arg);
    assert!(info_found.is_some(), "no signature help at the call site");
    if let Some(info) = info_found {
        assert!(info.label.contains("fun add"), "label: {}", info.label);
        assert_eq!(info.params.len(), 2);
        assert_eq!(info.active, 1, "active parameter should be the second");
    }
}

#[test]
fn borrow_notes_explain_inconsistent_paths() {
    let analysis = analyze(&fixture("explain_leak.cnb"), &[]);
    let rendered: Vec<String> = analysis.errors.iter().map(|diag| diag.0.clone()).collect();
    assert!(
        rendered.iter().any(|message| message.contains("consumed on some paths")),
        "expected a path-inconsistency error, got: {:?}",
        rendered
    );
    assert!(!analysis.notes.is_empty(), "no explanatory notes were attached");
    let mut idx = 0usize;
    while idx < analysis.notes.len() {
        match analysis.notes.get(idx) {
            Some(note) => {
                assert_ne!(note.2, NO_FILE, "note carries a fabricated span: {:?}", note.1);
                assert!(note.0 >= 0 && (note.0 as usize) < analysis.errors.len());
            }
            None => break,
        }
        idx += 1;
    }
}

#[test]
fn borrow_explanations_have_a_stable_json_surface() -> Result<(), Box<dyn Error>> {
    let output = Command::new(env!("CARGO_BIN_EXE_cinnabar"))
        .arg(fixture("explain_leak.cnb"))
        .arg("--explain-borrow=json")
        .output()?;
    assert!(!output.status.success(), "borrow-invalid input unexpectedly succeeded");
    let report: Value = serde_json::from_slice(&output.stdout)?;
    // The envelope is the compiler's one structured diagnostic surface, not
    // a borrow-specific one: `--explain-borrow=json` is the older spelling
    // of the request `--emit-json` makes for every stage.
    assert_eq!(
        report.get("format").and_then(Value::as_str),
        Some("cinnabar.diagnostics.v1")
    );
    let diagnostics = report
        .get("diagnostics")
        .and_then(Value::as_array)
        .ok_or("JSON borrow report had no diagnostics array")?;
    assert!(!diagnostics.is_empty(), "JSON borrow report was empty");
    let has_path_notes = diagnostics.iter().any(|diagnostic| {
        diagnostic
            .get("explanations")
            .and_then(Value::as_array)
            .is_some_and(|explanations| explanations.len() >= 2)
    });
    assert!(has_path_notes, "JSON borrow report omitted path explanations: {}", report);
    let every_source_is_real = diagnostics.iter().all(|diagnostic| {
        diagnostic
            .get("source")
            .and_then(|source| source.get("path"))
            .and_then(Value::as_str)
            .is_some_and(|path| path.ends_with("explain_leak.cnb"))
    });
    assert!(every_source_is_real, "JSON report contained a fabricated source: {}", report);
    Ok(())
}

#[test]
fn overlay_buffers_shadow_the_file_system() {
    let entry = fixture("multi_file/main.cnb");
    let broken = "use Math.add\n\npub fun main() I64\n  return add(10)\nend\n";
    let overlay = [(entry.clone(), broken.to_string())];
    let analysis = analyze(&entry, &overlay);
    assert!(
        !analysis.errors.is_empty(),
        "overlay with an arity error should fail to check"
    );
    // The same entry with the on-disk (valid) content stays clean.
    let clean = analyze(&entry, &[]);
    assert!(clean.errors.is_empty(), "on-disk fixture should be clean: {:?}", clean.errors);
}

#[test]
fn formatter_is_idempotent_and_preserves_the_reference_program() -> Result<(), Box<dyn Error>> {
    let entry = fixture("spec.cnb");
    let source = std::fs::read_to_string(&entry)?;
    let formatted = format_source(&source);
    assert_eq!(format_source(&formatted), formatted, "formatter was not idempotent");
    let overlay = [(entry.clone(), formatted)];
    let analysis = analyze(&entry, &overlay);
    assert!(analysis.resolved, "formatted source did not resolve: {:?}", analysis.errors);
    assert!(analysis.typechecked, "formatted source did not typecheck: {:?}", analysis.errors);
    assert!(analysis.errors.is_empty(), "formatting changed program validity: {:?}", analysis.errors);
    Ok(())
}

fn unique_project_directory() -> PathBuf {
    let timestamp = match SystemTime::now().duration_since(UNIX_EPOCH) {
        Ok(duration) => duration.as_nanos(),
        Err(time_error) => time_error.duration().as_nanos(),
    };
    std::env::temp_dir().join(format!(
        "cinnabar_tooling_project_{}_{}",
        std::process::id(),
        timestamp
    ))
}

#[test]
fn project_and_documentation_commands_work_end_to_end() -> Result<(), Box<dyn Error>> {
    let compiler = env!("CARGO_BIN_EXE_cinnabar");
    let project = unique_project_directory();
    let initialized = Command::new(compiler).arg("init").arg(&project).output()?;
    assert!(
        initialized.status.success(),
        "init failed: {}",
        String::from_utf8_lossy(&initialized.stderr)
    );

    std::fs::write(
        project.join("main.cnb"),
        "#! Project entry documentation\npub fun main() I64\n  return 0\nend\n",
    )?;
    let checked = Command::new(compiler).arg("check").arg(&project).output()?;
    assert!(checked.status.success(), "check failed: {}", String::from_utf8_lossy(&checked.stderr));

    let documented = Command::new(compiler).arg("doc").arg(&project).output()?;
    assert!(
        documented.status.success(),
        "doc failed: {}",
        String::from_utf8_lossy(&documented.stderr)
    );
    let html = std::fs::read_to_string(project.join("target").join("doc").join("index.html"))?;
    assert!(html.contains("Project entry documentation"));
    assert!(html.contains("main"));

    let built = Command::new(compiler).arg("build").arg(&project).output()?;
    assert!(built.status.success(), "build failed: {}", String::from_utf8_lossy(&built.stderr));
    let ran = Command::new(compiler).arg("run").arg(&project).output()?;
    assert!(ran.status.success(), "run failed: {}", String::from_utf8_lossy(&ran.stderr));

    std::fs::write(
        project.join("tests").join("invalid.reject.cnb"),
        "pub fun main() I64\n  return unknown_value\nend\n",
    )?;
    let updated = Command::new(compiler)
        .arg("test")
        .arg(&project)
        .arg("--update-snapshots")
        .output()?;
    assert!(
        updated.status.success(),
        "snapshot update failed: {}",
        String::from_utf8_lossy(&updated.stderr)
    );
    assert!(project.join("tests").join("invalid.reject.cnb.stderr").is_file());
    let tested = Command::new(compiler).arg("test").arg(&project).output()?;
    assert!(tested.status.success(), "test failed: {}", String::from_utf8_lossy(&tested.stderr));
    Ok(())
}

#[test]
fn folding_ranges_cover_module_and_function_bodies() {
    let entry = fixture("explain_leak.cnb");
    let analysis = analyze(&entry, &[]);
    assert!(analysis.resolved, "errors: {:?}", analysis.errors);
    let entry_file = file_id_of(&analysis, &entry);
    let text = analysis.files.first().map(|pair| pair.1.clone()).unwrap_or_default();
    let ranges = folding_ranges(&analysis, entry_file);
    assert!(!ranges.is_empty(), "expected at least one foldable range");
    // The module's span starts at `mod`, not at the `pub` modifier before it
    // (see the parser's item-span comments), so this looks for a range that
    // *contains* the module body rather than one starting exactly at `pub`.
    let mod_start = offset_of(&text, "mod Memory");
    assert!(mod_start >= 0);
    let has_module_range = ranges.iter().any(|(start, end)| {
        let slice = text.get(*start as usize..*end as usize).unwrap_or("");
        *start <= mod_start && slice.contains("allocate") && slice.contains("deallocate") && slice.ends_with("end")
    });
    assert!(has_module_range, "no fold range for the Memory module: {:?}", ranges);
    // A bodyless native declaration (no `end`) folds nothing.
    let nat_type_start = offset_of(&text, "pub nat type Block");
    assert!(nat_type_start >= 0);
    let has_native_range = ranges.iter().any(|(start, _)| *start == nat_type_start);
    assert!(!has_native_range, "a bodyless native type should not fold");
}

#[test]
fn document_symbols_nest_module_contents() {
    let entry = fixture("explain_leak.cnb");
    let analysis = analyze(&entry, &[]);
    assert!(analysis.resolved, "errors: {:?}", analysis.errors);
    let entry_file = file_id_of(&analysis, &entry);
    let symbols = document_symbols(&analysis, entry_file);
    let names: Vec<&str> = symbols.iter().map(|info| info.name.as_str()).collect();
    assert!(names.contains(&"Memory"), "top-level symbols: {:?}", names);
    assert!(names.contains(&"main"), "top-level symbols: {:?}", names);
    // `leak_on_one_path` is a private top-level fun, not nested in Memory.
    assert!(names.contains(&"leak_on_one_path"), "top-level symbols: {:?}", names);
    let memory = symbols.iter().find(|info| info.name == "Memory").expect("Memory symbol");
    let child_names: Vec<&str> = memory.children.iter().map(|child| child.name.as_str()).collect();
    assert!(child_names.contains(&"Block"), "Memory children: {:?}", child_names);
    assert!(child_names.contains(&"allocate"), "Memory children: {:?}", child_names);
    assert!(child_names.contains(&"deallocate"), "Memory children: {:?}", child_names);
    // `use` items are imports, not declarations, and are excluded everywhere.
    assert!(!names.iter().any(|name| name.contains("Memory.allocate")), "imports should not appear");
}

#[test]
fn workspace_symbols_find_declarations_across_files() {
    let entry = fixture("multi_file/main.cnb");
    let analysis = analyze(&entry, &[]);
    assert!(analysis.resolved, "errors: {:?}", analysis.errors);
    let found = workspace_symbols(&analysis, "add");
    assert!(!found.is_empty(), "expected 'add' to be found");
    let in_math = found.iter().any(|info| {
        analysis
            .files
            .get(info.span.0 as usize)
            .map(|pair| pair.0.ends_with("Math.cnb"))
            .unwrap_or(false)
    });
    assert!(in_math, "'add' should resolve into Math.cnb: {:?}", found.iter().map(|i| &i.name).collect::<Vec<_>>());
    // Case-insensitive, substring match.
    assert!(!workspace_symbols(&analysis, "ADD").is_empty());
    assert!(workspace_symbols(&analysis, "no_such_symbol_anywhere").is_empty());
}

#[test]
fn rename_edits_cover_every_occurrence_across_files() {
    let entry = fixture("multi_file/main.cnb");
    let analysis = analyze(&entry, &[]);
    assert!(analysis.resolved, "errors: {:?}", analysis.errors);
    let entry_file = file_id_of(&analysis, &entry);
    let main_text = analysis.files.first().map(|pair| pair.1.clone()).unwrap_or_default();
    let call_at = offset_of(&main_text, "add(10");
    let edits = rename_edits(&analysis, entry_file, call_at, "sum").expect("rename should succeed");
    // `use Math.add`'s own path segment, the call site, both in main.cnb,
    // plus the declaration in Math.cnb: an item carries one symbol for its
    // whole span, so `use`'s import path resolves the same symbol a use
    // site does (matching `hover`/`definition` on the same dispatch).
    assert_eq!(edits.len(), 3, "edits: {:?}", edits);
    let mut per_file: Vec<i64> = Vec::new();
    for (edit_file, start, end, new_text) in &edits {
        assert_eq!(new_text, "sum");
        let text = analysis.files.get(*edit_file as usize).map(|pair| pair.1.clone()).unwrap_or_default();
        let slice = text.get(*start as usize..*end as usize).unwrap_or("");
        assert_eq!(slice, "add", "renamed span did not cover exactly the identifier: {:?}", slice);
        per_file.push(*edit_file);
    }
    let main_edits = per_file.iter().filter(|file| **file == entry_file).count();
    assert_eq!(main_edits, 2, "expected two edits in main.cnb: {:?}", edits);
}

#[test]
fn rename_edits_refuse_a_position_with_no_symbol() {
    let entry = fixture("dead_code.cnb");
    let analysis = analyze(&entry, &[]);
    let entry_file = file_id_of(&analysis, &entry);
    let text = analysis.files.first().map(|pair| pair.1.clone()).unwrap_or_default();
    // Well inside the file's opening doc comment: comments carry no parse
    // node at all (see the module doc on `folding_ranges`), so nothing here
    // resolves a symbol to rename.
    let comment_at = offset_of(&text, "never used");
    assert!(comment_at >= 0);
    assert!(rename_edits(&analysis, entry_file, comment_at, "whatever").is_none());
}

#[test]
fn semantic_tokens_classify_a_function_call() {
    let entry = fixture("multi_file/main.cnb");
    let analysis = analyze(&entry, &[]);
    assert!(analysis.resolved, "errors: {:?}", analysis.errors);
    let entry_file = file_id_of(&analysis, &entry);
    let text = analysis.files.first().map(|pair| pair.1.clone()).unwrap_or_default();
    let call_at = offset_of(&text, "add(10");
    let tokens = semantic_tokens(&analysis, entry_file);
    let function_index = SEMANTIC_TOKEN_TYPES.iter().position(|name| *name == "function").unwrap() as i64;
    let matched = tokens
        .iter()
        .any(|(start, end, token_type)| *start == call_at && *end == call_at + 3 && *token_type == function_index);
    assert!(matched, "no function-typed token at the 'add' call site: {:?}", tokens);
}

#[test]
fn inlay_hints_report_inferred_type_for_unannotated_bindings() {
    let entry = fixture("tooling_scope.cnb");
    let analysis = analyze(&entry, &[]);
    assert!(analysis.resolved && analysis.typechecked, "errors: {:?}", analysis.errors);
    let entry_file = file_id_of(&analysis, &entry);
    let text = analysis.files.first().map(|pair| pair.1.clone()).unwrap_or_default();
    let hints = inlay_hints(&analysis, entry_file);
    assert!(!hints.is_empty(), "expected at least one inlay hint");
    let name_end = offset_of(&text, "only_then") + "only_then".len() as i64;
    let matched = hints.iter().find(|(offset, _)| *offset == name_end);
    let (_, label) = matched.expect("hint after 'only_then'");
    assert_eq!(label, ": I64");
}

#[test]
fn code_actions_remove_an_unused_import() {
    let source = "pub mod Tools\n  pub fun visible() I64\n    return 1\n  end\nend\n\nuse Tools.visible\n\npub fun main() I64\n  return Tools.visible()\nend\n";
    let path = fixture("synthetic_unused_import.cnb");
    let overlay = vec![(path.clone(), source.to_string())];
    let analysis = analyze(&path, &overlay);
    assert!(analysis.resolved, "errors: {:?}", analysis.errors);
    let entry_file = file_id_of(&analysis, &path);
    let fixes = code_actions(&analysis, entry_file, 0, source.len() as i64);
    let fix = fixes
        .iter()
        .find(|fix| fix.title.contains("unused import"))
        .unwrap_or_else(|| panic!("no unused-import fix among: {:?}", fixes.iter().map(|f| &f.title).collect::<Vec<_>>()));
    assert_eq!(fix.edits.len(), 1);
    let (edit_file, start, end, new_text) = &fix.edits[0];
    assert_eq!(*edit_file, entry_file);
    assert_eq!(new_text, "");
    let removed = source.get(*start as usize..*end as usize).unwrap_or("");
    assert!(removed.trim() == "use Tools.visible", "removed text: {:?}", removed);
}
