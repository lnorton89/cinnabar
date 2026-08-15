//! The arena dump behind `--dump-typed-ast`, in text and in JSON.
//!
//! Serializes the compiler's entire state once the front end has run: the
//! interning table, the list arena, and every node row with its raw slots
//! plus a symbolic annotation of what that row means — including the
//! attachments earlier stages computed, so resolved symbols, canonical type
//! keys, linearity flags, variant tags, and field facts all appear as the
//! stages left them.
//!
//! A row's annotation is extracted once, into `RowDetail`, and rendered
//! twice: as the line-oriented text a terminal reads, and as the object a
//! `--emit-json` consumer reads. Those are two spellings of one extraction,
//! not two readings of the arena — a second walk that decided for itself
//! what a row means could tell an editor something the terminal never said.
//!
//! **Invariants:**
//! - It prints facts the pipeline attached and never re-derives one. The
//!   dump's whole value is that it shows the compiler's actual state; a
//!   field this file computed for display would make it a second opinion
//!   rather than a window.
//! - Both renderings consume the same `RowDetail`. Neither may read a slot
//!   the other does not.

use crate::ast::*;
use crate::emit_json::{files_json, source_json};
use crate::typecheck::render_type_key;
use serde_json::{json, Map, Value};

pub fn dump_typed_arena(names: &[String], nodes: &[i64], lists: &[Vec<i64>]) -> String {
    let mut out = String::new();
    dump_names(names, &mut out);
    dump_lists(lists, &mut out);
    dump_nodes(names, nodes, lists, &mut out);
    out
}

/// The whole arena as one JSON document: the interning table, the list
/// arena, and every node row with its slots and extracted detail.
///
/// `format` names which stopping point produced it — the parse-only arena
/// or the fully attributed one — because the two documents have the same
/// shape and differ only in which attachment slots are still `-1`.
pub fn arena_json(
    names: &[String],
    nodes: &[i64],
    lists: &[Vec<i64>],
    root: i64,
    files: &[(String, String)],
    format: &str,
) -> Value {
    json!({
        "format": format,
        "root": root,
        "files": files_json(files),
        "names": names_json(names),
        "lists": lists_json(lists),
        "nodes": nodes_json(names, nodes, lists, files)
    })
}

fn names_json(names: &[String]) -> Vec<Value> {
    let mut out: Vec<Value> = Vec::new();
    let mut idx = 0usize;
    while idx < names.len() {
        match names.get(idx) {
            Some(text) => out.push(Value::String(text.clone())),
            None => break,
        }
        idx += 1;
    }
    out
}

fn lists_json(lists: &[Vec<i64>]) -> Vec<Value> {
    let mut out: Vec<Value> = Vec::new();
    let mut idx = 0usize;
    while idx < lists.len() {
        match lists.get(idx) {
            Some(items) => {
                let rendered: Vec<Value> = items.iter().map(|value| json!(value)).collect();
                out.push(Value::Array(rendered));
            }
            None => break,
        }
        idx += 1;
    }
    out
}

fn nodes_json(names: &[String], nodes: &[i64], lists: &[Vec<i64>], files: &[(String, String)]) -> Vec<Value> {
    let count = nodes.len() as i64 / NODE_STRIDE;
    let mut out: Vec<Value> = Vec::new();
    let mut id = 0i64;
    while id < count {
        out.push(node_json(names, nodes, lists, files, id));
        id += 1;
    }
    out
}

// The three leading slots are a source span on almost every row, but not on
// all of them: a type-descriptor row spends them on linearity flags the
// canonical-key lookup never compares.  `RowDetail::spanned` is what the
// extraction says about the row it just read, so `source` is present only
// where a location is real and the raw slots are always there either way.
fn node_json(names: &[String], nodes: &[i64], lists: &[Vec<i64>], files: &[(String, String)], id: i64) -> Value {
    let tag = node_tag(nodes, id);
    let detail = row_detail(names, nodes, lists, id, tag);
    let source = if detail.spanned {
        source_json(files, node_file(nodes, id), node_start(nodes, id), node_end(nodes, id))
    } else {
        Value::Null
    };
    json!({
        "id": id,
        "tag": tag_name(tag),
        "file": node_file(nodes, id),
        "start": node_start(nodes, id),
        "end": node_end(nodes, id),
        "source": source,
        "slots": {
            "a": node_a(nodes, id),
            "b": node_b(nodes, id),
            "c": node_c(nodes, id),
            "d": node_d(nodes, id),
            "e": node_e(nodes, id),
            "f": node_f(nodes, id)
        },
        "detail": detail_json(&detail)
    })
}

fn dump_names(names: &[String], out: &mut String) {
    out.push_str(&format!("== names ({}) ==\n", names.len()));
    let mut idx = 0usize;
    while idx < names.len() {
        match names.get(idx) {
            Some(text) => out.push_str(&format!("{}: {:?}\n", idx, text)),
            None => break,
        }
        idx += 1;
    }
}

fn dump_lists(lists: &[Vec<i64>], out: &mut String) {
    out.push_str(&format!("== lists ({}) ==\n", lists.len()));
    let mut idx = 0usize;
    while idx < lists.len() {
        match lists.get(idx) {
            Some(items) => {
                let rendered: Vec<String> = items.iter().map(|value| value.to_string()).collect();
                out.push_str(&format!("{}: [{}]\n", idx, rendered.join(", ")));
            }
            None => break,
        }
        idx += 1;
    }
}

fn dump_nodes(names: &[String], nodes: &[i64], lists: &[Vec<i64>], out: &mut String) {
    let count = nodes.len() as i64 / NODE_STRIDE;
    out.push_str(&format!("== nodes ({}) ==\n", count));
    let mut id = 0i64;
    while id < count {
        dump_node_row(names, nodes, lists, id, out);
        id += 1;
    }
}

fn dump_node_row(names: &[String], nodes: &[i64], lists: &[Vec<i64>], id: i64, out: &mut String) {
    let tag = node_tag(nodes, id);
    out.push_str(&format!(
        "#{} {} file={} span={}..{} a={} b={} c={} d={} e={} f={}",
        id,
        tag_name(tag),
        node_file(nodes, id),
        node_start(nodes, id),
        node_end(nodes, id),
        node_a(nodes, id),
        node_b(nodes, id),
        node_c(nodes, id),
        node_d(nodes, id),
        node_e(nodes, id),
        node_f(nodes, id),
    ));
    let detail = detail_text(&row_detail(names, nodes, lists, id, tag));
    if !detail.is_empty() {
        out.push_str(" ; ");
        out.push_str(&detail);
    }
    out.push('\n');
}

/// One extracted value from a row, in the form a reader needs it rather
/// than as the integer the slot holds.
enum DetailValue {
    /// An entry of the interning table.
    Name(String),
    /// A string literal's decoded bytes, which may contain a newline or a
    /// NUL and so cannot be shown raw in a line-oriented dump.
    Literal(String),
    /// Another row of this arena.
    Node(i64),
    /// A list in the list arena.
    List(i64),
    /// A plain number: a canonical key, a tag, a declaration index.
    Int(i64),
    /// A symbolic opcode name, already resolved from its integer.
    Tag(&'static str),
    /// A canonical type key together with the typechecker's rendering of it.
    Type(i64, String),
}

/// One named value of a row's detail.
///
/// `text_key` is what the terminal rendering labels it — empty where the
/// text form shows the value alone — and `json_key` is its field name in
/// the JSON rendering. They differ where the text form's spelling would
/// make an awkward object key, which is why one extraction can serve both.
struct DetailField {
    json_key: &'static str,
    text_key: &'static str,
    value: DetailValue,
}

/// What one arena row means: its category, its opcode, whether its leading
/// slots are a real source span, and the facts its payload slots carry.
struct RowDetail {
    kind: &'static str,
    subkind: &'static str,
    spanned: bool,
    fields: Vec<DetailField>,
}

fn keyed(key: &'static str, value: DetailValue) -> DetailField {
    DetailField { json_key: key, text_key: key, value }
}

fn bare(json_key: &'static str, value: DetailValue) -> DetailField {
    DetailField { json_key, text_key: "", value }
}

fn renamed(json_key: &'static str, text_key: &'static str, value: DetailValue) -> DetailField {
    DetailField { json_key, text_key, value }
}

fn row(kind: &'static str, subkind: &'static str, fields: Vec<DetailField>) -> RowDetail {
    RowDetail { kind, subkind, spanned: true, fields }
}

fn detail_text(detail: &RowDetail) -> String {
    if detail.kind.is_empty() {
        return String::new();
    }
    let mut out = detail.kind.to_string();
    if !detail.subkind.is_empty() {
        out.push(' ');
        out.push_str(detail.subkind);
    }
    for field in &detail.fields {
        out.push(' ');
        if !field.text_key.is_empty() {
            out.push_str(field.text_key);
            out.push('=');
        }
        out.push_str(&value_text(&field.value));
    }
    out
}

fn value_text(value: &DetailValue) -> String {
    match value {
        DetailValue::Name(text) => format!("'{}'", text),
        DetailValue::Literal(text) => format!("\"{}\"", escaped_literal_text(text)),
        DetailValue::Node(id) => format!("#{}", id),
        DetailValue::List(id) => format!("list#{}", id),
        DetailValue::Int(number) => number.to_string(),
        DetailValue::Tag(name) => name.to_string(),
        DetailValue::Type(key, rendered) => format!("{} '{}'", key, rendered),
    }
}

fn detail_json(detail: &RowDetail) -> Value {
    if detail.kind.is_empty() {
        return Value::Null;
    }
    let mut object = Map::new();
    object.insert("kind".to_string(), Value::String(detail.kind.to_string()));
    if !detail.subkind.is_empty() {
        object.insert("subkind".to_string(), Value::String(detail.subkind.to_string()));
    }
    for field in &detail.fields {
        object.insert(field.json_key.to_string(), value_json(&field.value));
    }
    Value::Object(object)
}

fn value_json(value: &DetailValue) -> Value {
    match value {
        DetailValue::Name(text) => Value::String(text.clone()),
        DetailValue::Literal(text) => Value::String(text.clone()),
        DetailValue::Node(id) => json!(id),
        DetailValue::List(id) => json!(id),
        DetailValue::Int(number) => json!(number),
        DetailValue::Tag(name) => Value::String(name.to_string()),
        DetailValue::Type(key, rendered) => json!({ "key": key, "rendered": rendered }),
    }
}

fn row_detail(names: &[String], nodes: &[i64], lists: &[Vec<i64>], id: i64, tag: i64) -> RowDetail {
    if tag == NODE_TOKEN {
        return token_detail(names, nodes, id);
    }
    if tag == NODE_ITEM {
        return item_detail(names, nodes, id);
    }
    if tag == NODE_FN {
        return row("fn", "", vec![bare("name", DetailValue::Name(name_text(names, node_a(nodes, id))))]);
    }
    if tag == NODE_PARAM {
        return row("param", "", vec![bare("name", DetailValue::Name(name_text(names, node_a(nodes, id))))]);
    }
    if tag == NODE_FIELD {
        return row("field", "", vec![bare("name", DetailValue::Name(name_text(names, node_a(nodes, id))))]);
    }
    if tag == NODE_VARIANT {
        return row(
            "variant",
            "",
            vec![
                bare("name", DetailValue::Name(name_text(names, node_a(nodes, id)))),
                keyed("sym", DetailValue::Node(variant_sym_of(nodes, id))),
            ],
        );
    }
    if tag == NODE_TY {
        return ty_detail(names, nodes, lists, id);
    }
    if tag == NODE_EXPR {
        return expr_detail(names, nodes, lists, id);
    }
    if tag == NODE_STMT {
        return stmt_detail(names, nodes, lists, id);
    }
    if tag == NODE_PAT {
        return pat_detail(names, nodes, lists, id);
    }
    if tag == NODE_SYM {
        return sym_detail(names, nodes, id);
    }
    if tag == NODE_TYINFO {
        return tyinfo_detail(names, nodes, lists, id);
    }
    if tag == NODE_INST {
        return row(
            "inst",
            "",
            vec![
                keyed("fn", DetailValue::Node(inst_fn_of(nodes, id))),
                renamed("mono_key", "mono-key", DetailValue::Int(inst_mono_of(nodes, id))),
            ],
        );
    }
    if tag == NODE_CONSTVAL {
        return row(
            "constval",
            "",
            vec![
                keyed("sym", DetailValue::Node(node_a(nodes, id))),
                keyed("value", DetailValue::Int(node_b(nodes, id))),
            ],
        );
    }
    if tag == NODE_DOC {
        return row(
            "doc",
            "",
            vec![
                keyed("target", DetailValue::Node(node_a(nodes, id))),
                keyed("parts", DetailValue::List(node_b(nodes, id))),
            ],
        );
    }
    if tag == NODE_TRAIT {
        return row(
            "trait-dispatch",
            "",
            vec![
                keyed("call", DetailValue::Node(node_a(nodes, id))),
                renamed("trait_sym", "trait-sym", DetailValue::Node(trait_call_trait(nodes, id))),
                keyed("method", DetailValue::Name(name_text(names, trait_call_method(nodes, id)))),
            ],
        );
    }
    if tag == NODE_VARFACT {
        return row(
            "varfact",
            "",
            vec![
                renamed("enum_key", "enum-key", DetailValue::Int(node_a(nodes, id))),
                keyed("variant", DetailValue::Name(name_text(names, node_b(nodes, id)))),
                keyed("tag", DetailValue::Int(node_d(nodes, id))),
            ],
        );
    }
    if tag == NODE_FIELDKEY {
        return row(
            "fieldkey",
            "",
            vec![
                renamed("struct_key", "struct-key", DetailValue::Int(node_a(nodes, id))),
                keyed("field", DetailValue::Name(name_text(names, node_b(nodes, id)))),
                renamed("field_key", "field-key", DetailValue::Int(fieldkey_key_of(nodes, id))),
                renamed("decl_index", "decl-idx", DetailValue::Int(fieldkey_idx_of(nodes, id))),
            ],
        );
    }
    row("", "", Vec::new())
}

fn token_detail(names: &[String], nodes: &[i64], id: i64) -> RowDetail {
    let kind = node_a(nodes, id);
    if kind == TOK_IDENT {
        return row("tok", "IDENT", vec![bare("name", DetailValue::Name(name_text(names, node_b(nodes, id))))]);
    }
    if kind == TOK_SYM {
        return row("tok", "SYM", vec![bare("name", DetailValue::Name(name_text(names, node_b(nodes, id))))]);
    }
    if kind == TOK_DOC {
        return row("tok", "DOC", vec![bare("name", DetailValue::Name(name_text(names, node_b(nodes, id))))]);
    }
    if kind == TOK_INT {
        return row("tok", "INT", vec![bare("value", DetailValue::Int(node_c(nodes, id)))]);
    }
    if kind == TOK_HEX {
        return row("tok", "HEX", vec![bare("value", DetailValue::Int(node_c(nodes, id)))]);
    }
    if kind == TOK_STRING {
        // The lexer decoded the escapes and interned the bytes, so the
        // token's payload is a name id like an identifier's, not a value.
        return row("tok", "STRING", vec![bare("value", DetailValue::Literal(name_text(names, node_b(nodes, id))))]);
    }
    if kind == TOK_NL {
        return row("tok", "NL", Vec::new());
    }
    if kind == TOK_EOF {
        return row("tok", "EOF", Vec::new());
    }
    row("tok", "?", Vec::new())
}

fn item_detail(names: &[String], nodes: &[i64], id: i64) -> RowDetail {
    let kind = node_a(nodes, id);
    let sym = item_sym_of(nodes, id);
    let mut fields: Vec<DetailField> = Vec::new();
    if kind == ITEM_MODULE
        || kind == ITEM_STRUCT
        || kind == ITEM_ENUM
        || kind == ITEM_TRAIT
        || kind == ITEM_CONST
        || kind == ITEM_NATIVE_TYPE
    {
        fields.push(bare("name", DetailValue::Name(name_text(names, node_d(nodes, id)))));
    }
    if sym != NONE {
        fields.push(keyed("sym", DetailValue::Node(sym)));
    }
    row("item", item_kind_name(kind), fields)
}

fn ty_detail(names: &[String], nodes: &[i64], lists: &[Vec<i64>], id: i64) -> RowDetail {
    let mut fields: Vec<DetailField> = Vec::new();
    let key = ty_key_of(nodes, id);
    if key != NONE {
        fields.push(keyed("key", DetailValue::Type(key, render_type_key(names, nodes, lists, key))));
    }
    let sym = ty_sym_of(nodes, id);
    if sym != NONE {
        fields.push(keyed("sym", DetailValue::Node(sym)));
    }
    row("ty", ty_kind_name(node_a(nodes, id)), fields)
}

fn expr_detail(names: &[String], nodes: &[i64], lists: &[Vec<i64>], id: i64) -> RowDetail {
    let mut fields: Vec<DetailField> = Vec::new();
    let ty = expr_ty_of(nodes, id);
    if ty != NONE {
        fields.push(keyed("ty", DetailValue::Type(ty, render_type_key(names, nodes, lists, ty))));
    }
    let sym = expr_sym_of(nodes, id);
    if sym != NONE {
        fields.push(keyed("sym", DetailValue::Node(sym)));
        fields.push(bare("sym_name", DetailValue::Name(name_text(names, node_b(nodes, sym)))));
    }
    row("expr", expr_kind_name(node_a(nodes, id)), fields)
}

fn stmt_detail(names: &[String], nodes: &[i64], lists: &[Vec<i64>], id: i64) -> RowDetail {
    let mut fields: Vec<DetailField> = Vec::new();
    let ty = stmt_ty_of(nodes, id);
    if ty != NONE {
        fields.push(keyed("ty", DetailValue::Type(ty, render_type_key(names, nodes, lists, ty))));
    }
    row("stmt", stmt_kind_name(node_a(nodes, id)), fields)
}

fn pat_detail(names: &[String], nodes: &[i64], lists: &[Vec<i64>], id: i64) -> RowDetail {
    let mut fields: Vec<DetailField> = Vec::new();
    let ty = pat_ty_of(nodes, id);
    if ty != NONE {
        fields.push(keyed("ty", DetailValue::Type(ty, render_type_key(names, nodes, lists, ty))));
    }
    let sym = pat_sym_of(nodes, id);
    if sym != NONE {
        fields.push(keyed("sym", DetailValue::Node(sym)));
    }
    row("pat", pat_kind_name(node_a(nodes, id)), fields)
}

fn sym_detail(names: &[String], nodes: &[i64], id: i64) -> RowDetail {
    row(
        "sym",
        sym_kind_name(node_a(nodes, id)),
        vec![
            bare("name", DetailValue::Name(name_text(names, node_b(nodes, id)))),
            keyed("decl", DetailValue::Node(node_c(nodes, id))),
        ],
    )
}

// A type-descriptor row is the one shape whose leading slots are not a
// span: the typechecker's linearity pass parks its flags in `file` and
// `start`, where the canonical-key lookup never compares them.  Reporting
// `spanned: false` is how a consumer learns that, instead of reading a
// linearity flag as a file id.
fn tyinfo_detail(names: &[String], nodes: &[i64], lists: &[Vec<i64>], id: i64) -> RowDetail {
    let key = node_a(nodes, id);
    RowDetail {
        kind: "tyinfo",
        subkind: "",
        spanned: false,
        fields: vec![
            keyed("key", DetailValue::Int(key)),
            renamed("descriptor", "kind", DetailValue::Tag(tyd_kind_name(node_b(nodes, id)))),
            keyed("linear", DetailValue::Int(node_file(nodes, id))),
            bare("rendered", DetailValue::Name(render_type_key(names, nodes, lists, key))),
        ],
    }
}

fn tag_name(tag: i64) -> &'static str {
    if tag == NODE_TOKEN {
        "TOKEN"
    } else if tag == NODE_ITEM {
        "ITEM"
    } else if tag == NODE_FN {
        "FN"
    } else if tag == NODE_PARAM {
        "PARAM"
    } else if tag == NODE_FIELD {
        "FIELD"
    } else if tag == NODE_VARIANT {
        "VARIANT"
    } else if tag == NODE_ARM {
        "ARM"
    } else if tag == NODE_TY {
        "TY"
    } else if tag == NODE_EXPR {
        "EXPR"
    } else if tag == NODE_STMT {
        "STMT"
    } else if tag == NODE_PAT {
        "PAT"
    } else if tag == NODE_SYM {
        "SYM"
    } else if tag == NODE_TYINFO {
        "TYINFO"
    } else if tag == NODE_INST {
        "INST"
    } else if tag == NODE_CONSTVAL {
        "CONSTVAL"
    } else if tag == NODE_DOC {
        "DOC"
    } else if tag == NODE_TRAIT {
        "TRAIT"
    } else if tag == NODE_VARFACT {
        "VARFACT"
    } else if tag == NODE_FIELDKEY {
        "FIELDKEY"
    } else {
        "?TAG"
    }
}

fn item_kind_name(kind: i64) -> &'static str {
    if kind == ITEM_MODULE {
        "MODULE"
    } else if kind == ITEM_USE {
        "USE"
    } else if kind == ITEM_STRUCT {
        "STRUCT"
    } else if kind == ITEM_ENUM {
        "ENUM"
    } else if kind == ITEM_TRAIT {
        "TRAIT"
    } else if kind == ITEM_IMPL {
        "IMPL"
    } else if kind == ITEM_FUN {
        "FUN"
    } else if kind == ITEM_NATIVE_FUN {
        "NATIVE_FUN"
    } else if kind == ITEM_CONST {
        "CONST"
    } else if kind == ITEM_NATIVE_TYPE {
        "NATIVE_TYPE"
    } else {
        "?ITEM"
    }
}

fn ty_kind_name(kind: i64) -> &'static str {
    if kind == TY_NAMED {
        "NAMED"
    } else if kind == TY_PATH {
        "PATH"
    } else if kind == TY_GENERIC {
        "GENERIC"
    } else if kind == TY_REF {
        "REF"
    } else if kind == TY_REF_MUT {
        "REF_MUT"
    } else if kind == TY_SLICE {
        "SLICE"
    } else if kind == TY_ARRAY {
        "ARRAY"
    } else if kind == TY_SELF {
        "SELF"
    } else if kind == TY_PARAM {
        "PARAM"
    } else {
        "?TY"
    }
}

pub fn expr_kind_name(kind: i64) -> &'static str {
    if kind == EXPR_LIT {
        "LIT"
    } else if kind == EXPR_PATH {
        "PATH"
    } else if kind == EXPR_UNARY {
        "UNARY"
    } else if kind == EXPR_BINARY {
        "BINARY"
    } else if kind == EXPR_CALL {
        "CALL"
    } else if kind == EXPR_STRUCT_LIT {
        "STRUCT_LIT"
    } else if kind == EXPR_ARRAY {
        "ARRAY"
    } else if kind == EXPR_MATCH {
        "MATCH"
    } else if kind == EXPR_TRY {
        "TRY"
    } else if kind == EXPR_INDEX {
        "INDEX"
    } else if kind == EXPR_FIELD_ACCESS {
        "FIELD_ACCESS"
    } else {
        "?EXPR"
    }
}

fn stmt_kind_name(kind: i64) -> &'static str {
    if kind == STMT_LET {
        "LET"
    } else if kind == STMT_ASSIGN {
        "ASSIGN"
    } else if kind == STMT_WHILE {
        "WHILE"
    } else if kind == STMT_IF {
        "IF"
    } else if kind == STMT_RETURN {
        "RETURN"
    } else if kind == STMT_BREAK {
        "BREAK"
    } else if kind == STMT_CONTINUE {
        "CONTINUE"
    } else if kind == STMT_EXPR {
        "EXPR"
    } else {
        "?STMT"
    }
}

fn pat_kind_name(kind: i64) -> &'static str {
    if kind == PAT_BIND {
        "BIND"
    } else if kind == PAT_PATH {
        "PATH"
    } else if kind == PAT_VARIANT {
        "VARIANT"
    } else if kind == PAT_ARRAY {
        "ARRAY"
    } else if kind == PAT_LIT {
        "LIT"
    } else {
        "?PAT"
    }
}

pub fn sym_kind_name(kind: i64) -> &'static str {
    if kind == SYM_MODULE {
        "MODULE"
    } else if kind == SYM_STRUCT {
        "STRUCT"
    } else if kind == SYM_ENUM {
        "ENUM"
    } else if kind == SYM_TRAIT {
        "TRAIT"
    } else if kind == SYM_TYPE {
        "TYPE"
    } else if kind == SYM_VARIANT {
        "VARIANT"
    } else if kind == SYM_FUN {
        "FUN"
    } else if kind == SYM_NATIVE_FUN {
        "NATIVE_FUN"
    } else if kind == SYM_CONST {
        "CONST"
    } else if kind == SYM_IMPL_METHOD {
        "IMPL_METHOD"
    } else if kind == SYM_TRAIT_METHOD {
        "TRAIT_METHOD"
    } else {
        "?SYM"
    }
}

fn tyd_kind_name(kind: i64) -> &'static str {
    if kind == TYD_UNKNOWN {
        "UNKNOWN"
    } else if kind == TYD_BUILTIN {
        "BUILTIN"
    } else if kind == TYD_STRUCT {
        "STRUCT"
    } else if kind == TYD_ENUM {
        "ENUM"
    } else if kind == TYD_NATIVE {
        "NATIVE"
    } else if kind == TYD_REF {
        "REF"
    } else if kind == TYD_REF_MUT {
        "REF_MUT"
    } else if kind == TYD_SLICE {
        "SLICE"
    } else if kind == TYD_ARRAY {
        "ARRAY"
    } else if kind == TYD_PARAM {
        "PARAM"
    } else if kind == TYD_MONO {
        "MONO"
    } else {
        "?TYD"
    }
}
