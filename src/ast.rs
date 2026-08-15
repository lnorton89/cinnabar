//! The flat node arena, and the accessors every stage reads it through.
//!
//! The whole compiler state is three allocation-only buffers rather than a
//! tree of heap-boxed Rust enums: `nodes`, a single arena of fixed-width
//! `NODE_STRIDE` rows holding every entity there is (tokens, items,
//! functions, types, expressions, statements, patterns, resolved symbols,
//! canonical type descriptors, monomorphization instances, trait-dispatch
//! facts, variant tags, field offsets); `names`, an interning table
//! addressed by integer id; and `lists`, an arena of variable-length id
//! lists. Every reference between entities is an integer index into one of
//! the three — there is no `Box`, and nothing here is walked recursively as
//! a Rust value.
//!
//! A row's meaning comes from its `NODE_TAG` plus, for most tags, a
//! secondary opcode in a payload slot (`ITEM_STRUCT`, `TY_REF`,
//! `EXPR_BINARY`/`BIN_ADD`, `STMT_IF`). The generic `node_a`..`node_f`
//! accessors and their `node_set_*` mutators are the only way rows are read
//! and written, which is what lets a later stage attach a fact to an entity
//! an earlier stage allocated without either of them owning a struct
//! definition the other has to be kept in step with.
//!
//! `Diag` and `Note` live here for the same reason: a diagnostic and its
//! supporting notes are facts about arena rows, and every stage produces
//! them in one shape for the driver to render.
//!
//! **Invariants:**
//! - A fact with nowhere of its own to live goes in an otherwise-unused
//!   payload slot of the row it describes, never in a new side table. That
//!   is what keeps the Single-Fact Rule cheap enough to actually follow as
//!   the language grows.
//! - `NO_FILE` marks a genuinely source-less fact. Every other span is the
//!   real origin of the thing it describes, carried unmodified from lexing
//!   through codegen; no stage may substitute a placeholder.
//! - A `Note` span is a site the producing stage actually visited — a
//!   binding site, a path's last move, a branch exit — never one invented
//!   to have something to point at.

pub type Diag = (String, i64, i64, i64);

// A secondary explanatory note attached to a primary diagnostic:
// (index of the diagnostic in the errors vec at attach time, message,
// file, start, end, kind).  Notes carry real source spans of facts the
// checker already computed (a binding site, a path's last move, a branch
// exit) — never fabricated locations.  Rendering is the consumer's choice:
// the CLI shows them as secondary labels under --explain-borrow, the
// language server as related information.
pub type Note = (i64, String, i64, i64, i64, i64);

// What role a note plays in the explanation, assigned by the stage that
// raised it.  The message is prose meant for a reader and is free to be
// reworded; the kind is what a tool may branch on, so an editor drawing a
// value's path through a function does not have to recognize the checker's
// sentences to know which span is the binding and which is a consuming
// branch.  A note whose role is not one of these is NOTE_CONTEXT: it
// supports the diagnostic without making a claim about a linear value's
// flow.
pub const NOTE_CONTEXT: i64 = 0;
pub const NOTE_BINDING: i64 = 1; // where the value under discussion was bound
pub const NOTE_CONSUMED: i64 = 2; // a path along which it is consumed
pub const NOTE_LIVE: i64 = 3; // a path along which it is still live
pub const NOTE_MOVED: i64 = 4; // a site that already moved it
pub const NOTE_GUIDANCE: i64 = 5; // what to do about it, at the site to do it

/// The symbolic name of a note kind, for the surfaces that report one.
pub fn note_kind_name(kind: i64) -> &'static str {
    if kind == NOTE_BINDING {
        "binding"
    } else if kind == NOTE_CONSUMED {
        "consumed"
    } else if kind == NOTE_LIVE {
        "live"
    } else if kind == NOTE_MOVED {
        "moved"
    } else if kind == NOTE_GUIDANCE {
        "guidance"
    } else {
        "context"
    }
}

// Attach a note to the most recently pushed diagnostic.  A note with no
// diagnostic to explain is dropped rather than invented.
pub fn push_note_for_last(errors: &[Diag], notes: &mut Vec<Note>, message: &str, file: i64, start: i64, end: i64, kind: i64) {
    if errors.is_empty() {
        return;
    }
    notes.push((errors.len() as i64 - 1, message.to_string(), file, start, end, kind));
}

pub const NONE: i64 = -1;
pub const NO_FILE: i64 = -1;

pub const NODE_STRIDE: i64 = 10;
pub const NODE_TAG: i64 = 0;
pub const NODE_FILE: i64 = 1;
pub const NODE_START: i64 = 2;
pub const NODE_END: i64 = 3;
pub const NODE_A: i64 = 4;
pub const NODE_B: i64 = 5;
pub const NODE_C: i64 = 6;
pub const NODE_D: i64 = 7;
pub const NODE_E: i64 = 8;
pub const NODE_F: i64 = 9;

pub const NODE_TOKEN: i64 = 0;
pub const NODE_ITEM: i64 = 1;
pub const NODE_FN: i64 = 2;
pub const NODE_PARAM: i64 = 3;
pub const NODE_FIELD: i64 = 4;
pub const NODE_VARIANT: i64 = 5;
pub const NODE_ARM: i64 = 6;
pub const NODE_TY: i64 = 7;
pub const NODE_EXPR: i64 = 8;
pub const NODE_STMT: i64 = 9;
pub const NODE_PAT: i64 = 10;
pub const NODE_SYM: i64 = 11;
pub const NODE_TYINFO: i64 = 12;
pub const NODE_INST: i64 = 13;
pub const NODE_CONSTVAL: i64 = 14;
pub const NODE_DOC: i64 = 20;

// Token rows.  (tag=NODE_TOKEN, a=kind, b=name, c=value).

pub const TOK_IDENT: i64 = 0; // identifier or keyword, by interned name
pub const TOK_INT: i64 = 1; // decimal integer literal
pub const TOK_HEX: i64 = 2; // hexadecimal literal (0x...)
pub const TOK_EOF: i64 = 3;
pub const TOK_NL: i64 = 4; // newline (statement boundary)
pub const TOK_SYM: i64 = 5; // operator or punctuation symbol, by interned name
pub const TOK_DOC: i64 = 6; // documentation comment body, by interned name
pub const TOK_STRING: i64 = 7; // string literal, escapes decoded, by interned name

// Documentation attachment rows. (tag=NODE_DOC, a=target node, b=doc name-id list).
// The lexer records comment bodies once and the parser attaches each consecutive
// group to the declaration it precedes. Consumers never rescan source comments.

// Item rows.  (tag=NODE_ITEM, a=kind, b=is_pub, c=sym, d..f kind-specific).

pub const ITEM_MODULE: i64 = 0; // d: name, e: child item id list
pub const ITEM_USE: i64 = 1; // d: path segments name-id list, e: alias name (NONE)
pub const ITEM_STRUCT: i64 = 2; // d: name, e: field id list, f: type param name-id list
pub const ITEM_ENUM: i64 = 3; // d: name, e: variant id list, f: type param name-id list
pub const ITEM_TRAIT: i64 = 4; // d: name, e: method fn id list, f: type param name-id list
pub const ITEM_IMPL: i64 = 5; // d: trait path name-id list, e: for-type id, f: method fn id list
pub const ITEM_FUN: i64 = 6; // d: fn id
pub const ITEM_NATIVE_FUN: i64 = 7; // d: fn id
pub const ITEM_CONST: i64 = 8; // d: name, e: type id, f: value expr id
pub const ITEM_NATIVE_TYPE: i64 = 9; // d: name, e: type param name-id list

// Function rows.  (tag=NODE_FN, a=name, b=type_param_list, c=param_list, d=ret_ty, e=is_impure, f=body_stmt_list).
// Parameter rows.  (tag=NODE_PARAM, a=name, b=ty).
// Struct-field rows.  (tag=NODE_FIELD, a=name, b=ty, c=is_pub).
// Enum-variant rows.  (tag=NODE_VARIANT, a=name, b=payload_type_list, c=is_pub).
// Match-arm rows.  (tag=NODE_ARM, a=pattern, b=body_stmt_list).
// Type rows.  (tag=NODE_TY, a=kind, b..c kind-specific).

pub const TY_NAMED: i64 = 0; // b: name id
pub const TY_PATH: i64 = 1; // b: segments name-id list
pub const TY_GENERIC: i64 = 2; // b: segments name-id list, c: argument type-id list
pub const TY_REF: i64 = 3; // b: inner type id
pub const TY_REF_MUT: i64 = 4; // b: inner type id
pub const TY_SLICE: i64 = 5; // b: element type id; `[T]`
pub const TY_ARRAY: i64 = 6; // b: element type id, c: length; `[T; N]`
pub const TY_SELF: i64 = 7; // `Self` inside a trait signature
pub const TY_PARAM: i64 = 8; // b: name id, c: trait-bound path segments list (NONE)

// Expression rows.  (tag=NODE_EXPR, a=kind, b..d kind-specific, e=ty, f=sym).

pub const EXPR_LIT: i64 = 0; // b: literal kind, c: value
pub const EXPR_PATH: i64 = 1; // b: segments name-id list; name references, callees, field chains
pub const EXPR_UNARY: i64 = 2; // b: unary op, c: operand expr id
pub const EXPR_BINARY: i64 = 3; // b: binary op, c: lhs expr id, d: rhs expr id
pub const EXPR_CALL: i64 = 4; // b: callee expr id, c: type-arg type-id list (NONE), d: arg expr-id list
pub const EXPR_STRUCT_LIT: i64 = 5; // b: path segments name-id list, c: field name-id list, d: field value expr-id list
pub const EXPR_ARRAY: i64 = 6; // b: element expr-id list
pub const EXPR_MATCH: i64 = 7; // b: scrutinee expr id, c: arm ids list
pub const EXPR_TRY: i64 = 8; // b: inner expr id
pub const EXPR_INDEX: i64 = 9; // b: base expr id, c: index expr id, d: fallibility flag (INDEX_*)

// Slot-d flag on EXPR_INDEX rows.  The typechecker attaches this fact once,
// and codegen reads it rather than re-deriving fallibility from the shape of
// the result type: an array whose element is itself a `Result` is infallible
// when indexed by a compile-time-proven constant, even though its result type
// is a `Result`.  `INDEX_FALLIBLE` marks a runtime or slice index typed as
// `Result(T, IndexError)`; `INDEX_INFALLIBLE` marks a constant array index
// typed as the bare element type.
pub const INDEX_INFALLIBLE: i64 = 0;
pub const INDEX_FALLIBLE: i64 = 1;
pub const EXPR_FIELD_ACCESS: i64 = 10; // b: base expr id, c: field name id; `expr.field` on a non-path base

pub const LIT_INT: i64 = 0;
pub const LIT_HEX: i64 = 1;
pub const LIT_TRUE: i64 = 2;
pub const LIT_FALSE: i64 = 3;
// A string literal.  Its `c` slot holds the interned name id of the
// *decoded* bytes (escapes already applied), not a numeric value: the
// literal's value is a byte sequence, and the name table is the arena that
// already stores byte sequences.  Interning also means two identical
// literals share one id, which is what lets codegen emit one `.rodata`
// global per distinct literal.
pub const LIT_STRING: i64 = 4;

pub const UN_NEG: i64 = 0;
pub const UN_NOT: i64 = 1;
pub const UN_REF: i64 = 2;
pub const UN_REF_MUT: i64 = 3;

pub const BIN_ADD: i64 = 0;
pub const BIN_SUB: i64 = 1;
pub const BIN_MUL: i64 = 2;
pub const BIN_DIV: i64 = 3;
pub const BIN_SHL: i64 = 4;
pub const BIN_SHR: i64 = 5;
pub const BIN_BAND: i64 = 6;
pub const BIN_BOR: i64 = 7;
pub const BIN_BXOR: i64 = 8;
pub const BIN_EQ: i64 = 9;
pub const BIN_NE: i64 = 10;
pub const BIN_LT: i64 = 11;
pub const BIN_GT: i64 = 12;
pub const BIN_LE: i64 = 13;
pub const BIN_GE: i64 = 14;
pub const BIN_AND: i64 = 15;
pub const BIN_OR: i64 = 16;
pub const BIN_MOD: i64 = 17;

// Statement rows.  (tag=NODE_STMT, a=kind, b..e kind-specific, f=ty).

pub const STMT_LET: i64 = 0; // b: is_mut, c: name id, d: type id (NONE), e: init expr id
pub const STMT_ASSIGN: i64 = 1; // b: target expr id (a place: name, field chain, or field through a &mut reference), c: value expr id
pub const STMT_WHILE: i64 = 2; // b: cond expr id, c: body stmt-id list
pub const STMT_IF: i64 = 3; // b: cond expr id, c: then stmt-id list, d: else stmt-id list (NONE)
pub const STMT_RETURN: i64 = 4; // b: value expr id (NONE)
pub const STMT_BREAK: i64 = 5;
pub const STMT_CONTINUE: i64 = 6;
pub const STMT_EXPR: i64 = 7; // b: expr id; includes `match`, `try`, and bare calls as statements

// Pattern rows.  (tag=NODE_PAT, a=kind, b..c kind-specific, d=ty).

pub const PAT_BIND: i64 = 0; // b: bound name id
pub const PAT_PATH: i64 = 1; // b: segments name-id list; unit variant such as `None`
pub const PAT_VARIANT: i64 = 2; // b: segments name-id list, c: payload pattern-id list
pub const PAT_ARRAY: i64 = 3; // b: element pattern-id list, c: rest binder name id (NONE)
pub const PAT_LIT: i64 = 4; // b: literal kind, c: value

// Symbol rows.  (tag=NODE_SYM, a=kind, b=name, c=decl).

pub const SYM_MODULE: i64 = 0;
pub const SYM_STRUCT: i64 = 1;
pub const SYM_ENUM: i64 = 2;
pub const SYM_TRAIT: i64 = 3;
pub const SYM_TYPE: i64 = 4; // native types
pub const SYM_VARIANT: i64 = 5;
pub const SYM_FUN: i64 = 6;
pub const SYM_NATIVE_FUN: i64 = 7;
pub const SYM_CONST: i64 = 8;
pub const SYM_IMPL_METHOD: i64 = 9;
pub const SYM_TRAIT_METHOD: i64 = 10;

// Slot-f flag on SYM_FUN rows: 1 marks the program entry point (`main`),
// assigned by the resolver so codegen never re-derives it from the name.
pub const SYM_FUN_MAIN: i64 = 1;

pub fn intern(names: &mut Vec<String>, text: &str) -> i64 {
    let mut idx = 0i64;
    while idx < names.len() as i64 {
        match names.get(idx as usize) {
            Some(existing) => {
                if *existing == text {
                    return idx;
                }
            }
            None => break,
        }
        idx += 1;
    }
    names.push(text.to_string());
    names.len() as i64 - 1
}

pub fn name_is(names: &[String], id: i64, text: &str) -> bool {
    match names.get(id as usize) {
        Some(existing) => *existing == text,
        None => false,
    }
}

pub fn name_text(names: &[String], id: i64) -> String {
    match names.get(id as usize) {
        Some(text) => text.clone(),
        None => String::new(),
    }
}

/// Renders a string literal's decoded bytes back into the source form that
/// would produce them, escaping exactly the five sequences the language
/// defines.
///
/// Every tool that shows a literal goes through this: a decoded literal can
/// contain a newline or a NUL, which would break a line-oriented dump or
/// make it non-text, and a reader needs to tell a real newline from the two
/// characters that produced it.
pub fn escaped_literal_text(text: &str) -> String {
    let mut out = String::new();
    for ch in text.chars() {
        if ch == '\n' {
            out.push_str("\\n");
        } else if ch == '\t' {
            out.push_str("\\t");
        } else if ch == '\0' {
            out.push_str("\\0");
        } else if ch == '"' {
            out.push_str("\\\"");
        } else if ch == '\\' {
            out.push_str("\\\\");
        } else {
            out.push(ch);
        }
    }
    out
}

pub fn find_name(names: &[String], text: &str) -> i64 {
    let mut idx = 0i64;
    while idx < names.len() as i64 {
        match names.get(idx as usize) {
            Some(existing) => {
                if *existing == text {
                    return idx;
                }
            }
            None => break,
        }
        idx += 1;
    }
    NONE
}

pub fn join_path(names: &[String], ids: &[i64]) -> String {
    let mut parts: Vec<String> = Vec::new();
    let mut idx = 0i64;
    while idx < ids.len() as i64 {
        match ids.get(idx as usize) {
            Some(id) => parts.push(name_text(names, *id)),
            None => break,
        }
        idx += 1;
    }
    parts.join(".")
}

pub fn alloc_list(lists: &mut Vec<Vec<i64>>) -> i64 {
    lists.push(Vec::new());
    lists.len() as i64 - 1
}

pub fn list_push(lists: &mut [Vec<i64>], list_id: i64, value: i64) -> bool {
    match lists.get_mut(list_id as usize) {
        Some(list) => {
            list.push(value);
            true
        }
        None => false,
    }
}

pub fn node_get(nodes: &[i64], id: i64, offset: i64) -> i64 {
    let slot = match id.checked_mul(NODE_STRIDE).and_then(|base| base.checked_add(offset)) {
        Some(slot) => slot,
        None => return NONE,
    };
    if slot < 0 {
        return NONE;
    }
    match nodes.get(slot as usize) {
        Some(value) => *value,
        None => NONE,
    }
}

pub fn node_set(nodes: &mut [i64], id: i64, offset: i64, value: i64) -> bool {
    let slot = match id.checked_mul(NODE_STRIDE).and_then(|base| base.checked_add(offset)) {
        Some(slot) => slot,
        None => return false,
    };
    if slot < 0 {
        return false;
    }
    match nodes.get_mut(slot as usize) {
        Some(cell) => {
            *cell = value;
            true
        }
        None => false,
    }
}

pub fn alloc_node(nodes: &mut Vec<i64>, fields: &[i64]) -> i64 {
    let id = nodes.len() as i64 / NODE_STRIDE;
    let mut idx = 0i64;
    while idx < NODE_STRIDE {
        let value = match fields.get(idx as usize) {
            Some(field) => *field,
            None => NONE,
        };
        nodes.push(value);
        idx += 1;
    }
    id
}

pub fn node_tag(nodes: &[i64], id: i64) -> i64 {
    node_get(nodes, id, NODE_TAG)
}

pub fn node_file(nodes: &[i64], id: i64) -> i64 {
    node_get(nodes, id, NODE_FILE)
}

pub fn node_start(nodes: &[i64], id: i64) -> i64 {
    node_get(nodes, id, NODE_START)
}

pub fn node_end(nodes: &[i64], id: i64) -> i64 {
    node_get(nodes, id, NODE_END)
}

pub fn node_a(nodes: &[i64], id: i64) -> i64 {
    node_get(nodes, id, NODE_A)
}

pub fn node_b(nodes: &[i64], id: i64) -> i64 {
    node_get(nodes, id, NODE_B)
}

pub fn node_c(nodes: &[i64], id: i64) -> i64 {
    node_get(nodes, id, NODE_C)
}

pub fn node_d(nodes: &[i64], id: i64) -> i64 {
    node_get(nodes, id, NODE_D)
}

pub fn node_e(nodes: &[i64], id: i64) -> i64 {
    node_get(nodes, id, NODE_E)
}

pub fn node_f(nodes: &[i64], id: i64) -> i64 {
    node_get(nodes, id, NODE_F)
}

pub fn node_set_a(nodes: &mut [i64], id: i64, value: i64) -> bool {
    node_set(nodes, id, NODE_A, value)
}

pub fn node_set_b(nodes: &mut [i64], id: i64, value: i64) -> bool {
    node_set(nodes, id, NODE_B, value)
}

pub fn node_set_c(nodes: &mut [i64], id: i64, value: i64) -> bool {
    node_set(nodes, id, NODE_C, value)
}

pub fn node_set_d(nodes: &mut [i64], id: i64, value: i64) -> bool {
    node_set(nodes, id, NODE_D, value)
}

pub fn node_set_e(nodes: &mut [i64], id: i64, value: i64) -> bool {
    node_set(nodes, id, NODE_E, value)
}

pub fn node_set_f(nodes: &mut [i64], id: i64, value: i64) -> bool {
    node_set(nodes, id, NODE_F, value)
}

pub fn tok_is_name(nodes: &[i64], names: &[String], id: i64, text: &str) -> bool {
    node_tag(nodes, id) == NODE_TOKEN
        && node_a(nodes, id) == TOK_IDENT
        && name_is(names, node_b(nodes, id), text)
}

pub fn tok_is_sym(nodes: &[i64], names: &[String], id: i64, text: &str) -> bool {
    node_tag(nodes, id) == NODE_TOKEN
        && node_a(nodes, id) == TOK_SYM
        && name_is(names, node_b(nodes, id), text)
}

pub fn item_is_pub(nodes: &[i64], id: i64) -> i64 {
    node_b(nodes, id)
}

pub fn item_sym_of(nodes: &[i64], id: i64) -> i64 {
    node_c(nodes, id)
}

pub fn item_set_sym(nodes: &mut [i64], id: i64, sym: i64) -> bool {
    node_set_c(nodes, id, sym)
}

pub fn expr_ty_of(nodes: &[i64], id: i64) -> i64 {
    node_e(nodes, id)
}

pub fn expr_set_ty(nodes: &mut [i64], id: i64, ty: i64) -> bool {
    node_set_e(nodes, id, ty)
}

pub fn expr_sym_of(nodes: &[i64], id: i64) -> i64 {
    node_f(nodes, id)
}

pub fn expr_set_sym(nodes: &mut [i64], id: i64, sym: i64) -> bool {
    node_set_f(nodes, id, sym)
}

pub fn stmt_ty_of(nodes: &[i64], id: i64) -> i64 {
    node_f(nodes, id)
}

pub fn stmt_set_ty(nodes: &mut [i64], id: i64, ty: i64) -> bool {
    node_set_f(nodes, id, ty)
}

pub fn pat_ty_of(nodes: &[i64], id: i64) -> i64 {
    node_d(nodes, id)
}

pub fn pat_set_ty(nodes: &mut [i64], id: i64, ty: i64) -> bool {
    node_set_d(nodes, id, ty)
}

pub fn pat_sym_of(nodes: &[i64], id: i64) -> i64 {
    node_e(nodes, id)
}

pub fn pat_set_sym(nodes: &mut [i64], id: i64, sym: i64) -> bool {
    node_set_e(nodes, id, sym)
}

pub fn pat_rest_key_of(nodes: &[i64], id: i64) -> i64 {
    node_f(nodes, id)
}

pub fn pat_set_rest_key(nodes: &mut [i64], id: i64, key: i64) -> bool {
    node_set_f(nodes, id, key)
}

pub fn variant_sym_of(nodes: &[i64], id: i64) -> i64 {
    node_d(nodes, id)
}

pub fn variant_set_sym(nodes: &mut [i64], id: i64, sym: i64) -> bool {
    node_set_d(nodes, id, sym)
}

pub fn sym_native_op(nodes: &[i64], sym: i64) -> i64 {
    node_f(nodes, sym)
}

pub fn sym_set_native_op(nodes: &mut [i64], sym: i64, op: i64) -> bool {
    node_set_f(nodes, sym, op)
}

pub fn sym_prim_kind(nodes: &[i64], sym: i64) -> i64 {
    node_f(nodes, sym)
}

pub fn sym_set_prim_kind(nodes: &mut [i64], sym: i64, kind: i64) -> bool {
    node_set_f(nodes, sym, kind)
}

pub fn ty_key_of(nodes: &[i64], id: i64) -> i64 {
    node_d(nodes, id)
}

pub fn ty_set_key(nodes: &mut [i64], id: i64, key: i64) -> bool {
    node_set_d(nodes, id, key)
}

pub fn ty_sym_of(nodes: &[i64], id: i64) -> i64 {
    node_e(nodes, id)
}

pub fn ty_set_sym(nodes: &mut [i64], id: i64, sym: i64) -> bool {
    node_set_e(nodes, id, sym)
}

// Type-descriptor rows.  (tag=NODE_TYINFO, a=key, b=kind, c=sym, d=args list, e=element key, f=len/bound/sub-kind).
// Native rows carry the has_linear_elements flag (0/1) in the start slot,
// attached by the typechecker's linearity pass into a slot the canonical-key
// lookup never compares.

pub const TYD_UNKNOWN: i64 = 0;
pub const TYD_BUILTIN: i64 = 1;
pub const TYD_STRUCT: i64 = 2;
pub const TYD_ENUM: i64 = 3;
pub const TYD_NATIVE: i64 = 4;
pub const TYD_REF: i64 = 5;
pub const TYD_REF_MUT: i64 = 6;
pub const TYD_SLICE: i64 = 7;
pub const TYD_ARRAY: i64 = 8;
pub const TYD_PARAM: i64 = 9;
pub const TYD_MONO: i64 = 10; // (fn node, type-arg keys): one key per monomorphized function

// Builtin scalar sub-kinds.  Stored in slot `f` of TYD_BUILTIN descriptor
// rows at seed time; every later stage classifies scalars from this
// integer, never from the symbol's name.  The width, signedness, and
// two's-complement mask of each sub-kind are the single definitions in
// `builtin_int_width` / `builtin_int_is_signed` / `builtin_int_mask`;
// the typechecker and codegen both read those helpers, never a name.
pub const BUILTIN_I8: i64 = 0;
pub const BUILTIN_I16: i64 = 1;
pub const BUILTIN_I32: i64 = 2;
pub const BUILTIN_I64: i64 = 3;
pub const BUILTIN_ISIZE: i64 = 4;
pub const BUILTIN_U8: i64 = 5;
pub const BUILTIN_U16: i64 = 6;
pub const BUILTIN_U32: i64 = 7;
pub const BUILTIN_U64: i64 = 8;
pub const BUILTIN_USIZE: i64 = 9;
pub const BUILTIN_BOOL: i64 = 10;

// The bit width of a builtin integer sub-kind.  Isize/Usize are the
// target pointer width (64 on x86_64/AArch64).  Non-integer sub-kinds
// report 0; callers only consult this for `builtin_int_is_int` sub-kinds.
pub fn builtin_int_width(sub: i64) -> u32 {
    if sub == BUILTIN_I8 || sub == BUILTIN_U8 {
        8
    } else if sub == BUILTIN_I16 || sub == BUILTIN_U16 {
        16
    } else if sub == BUILTIN_I32 || sub == BUILTIN_U32 {
        32
    } else if sub == BUILTIN_I64
        || sub == BUILTIN_ISIZE
        || sub == BUILTIN_U64
        || sub == BUILTIN_USIZE
    {
        64
    } else {
        0
    }
}

// True when the sub-kind is one of the ten integer types (Bool is not).
pub fn builtin_int_is_int(sub: i64) -> bool {
    builtin_int_width(sub) != 0
}

// True when the sub-kind is a signed integer (I8..Isize).
pub fn builtin_int_is_signed(sub: i64) -> bool {
    sub == BUILTIN_I8
        || sub == BUILTIN_I16
        || sub == BUILTIN_I32
        || sub == BUILTIN_I64
        || sub == BUILTIN_ISIZE
}

// The two's-complement low-`width`-bit mask for a sub-kind.
pub fn builtin_int_mask(sub: i64) -> u64 {
    let width = builtin_int_width(sub);
    if width >= 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    }
}

pub const NAT_NONE: i64 = 0;
pub const NAT_INT_FROM: i64 = 1;
pub const NAT_SLICE_LEN: i64 = 2;
pub const NAT_MEM_ALLOCATE: i64 = 3;
pub const NAT_MEM_DEALLOCATE: i64 = 4;
pub const NAT_MEM_WRITE_U8: i64 = 5;
pub const NAT_MEM_READ_U8: i64 = 6;
pub const NAT_VEC_NEW: i64 = 7;
pub const NAT_VEC_PUSH: i64 = 8;
pub const NAT_SLICE_VIEW: i64 = 36;
pub const NAT_VEC_FREE: i64 = 10;
pub const NAT_STRING_FROM_SLICE: i64 = 11;
pub const NAT_STRING_LEN: i64 = 12;
pub const NAT_STRING_FREE: i64 = 13;
pub const NAT_HASH_MAP_NEW: i64 = 14;
pub const NAT_HASH_MAP_INSERT: i64 = 15;
pub const NAT_HASH_MAP_GET: i64 = 16;
pub const NAT_HASH_MAP_FREE: i64 = 17;
pub const NAT_SELF_CHECK: i64 = 18;
pub const NAT_TERM_PRINT: i64 = 19;
pub const NAT_TERM_PRINT_LINE: i64 = 20;
pub const NAT_TERM_EPRINT: i64 = 21;
pub const NAT_NET_SOCKET: i64 = 22;
pub const NAT_NET_BIND: i64 = 23;
pub const NAT_NET_LISTEN: i64 = 24;
pub const NAT_NET_ACCEPT: i64 = 25;
pub const NAT_NET_SEND: i64 = 26;
pub const NAT_NET_CLOSE: i64 = 27;
pub const NAT_VEC_POP: i64 = 28;
pub const NAT_HASH_MAP_REMOVE: i64 = 29;
pub const NAT_FILE_OPEN: i64 = 30;
pub const NAT_FILE_READ: i64 = 31;
pub const NAT_FILE_WRITE: i64 = 32;
pub const NAT_FILE_CLOSE: i64 = 33;
pub const NAT_TERM_READ_LINE: i64 = 34;
pub const NAT_RUNTIME_ARGS: i64 = 35;
pub const NAT_PROCESS_SPAWN: i64 = 37;
pub const NAT_PROCESS_WAIT: i64 = 38;

/// The source spelling of a binary operator opcode.  Every stage that names
/// an operator in a diagnostic reads it from here, so a message from the
/// typechecker and one from codegen cannot disagree about what `BIN_SHL` is
/// called.
pub fn op_text(op: i64) -> &'static str {
    if op == BIN_ADD {
        "+"
    } else if op == BIN_SUB {
        "-"
    } else if op == BIN_MUL {
        "*"
    } else if op == BIN_DIV {
        "/"
    } else if op == BIN_MOD {
        "%"
    } else if op == BIN_SHL {
        "<<"
    } else if op == BIN_SHR {
        ">>"
    } else if op == BIN_BAND {
        "&"
    } else if op == BIN_BOR {
        "|"
    } else if op == BIN_BXOR {
        "^"
    } else if op == BIN_EQ {
        "=="
    } else if op == BIN_NE {
        "!="
    } else if op == BIN_LT {
        "<"
    } else if op == BIN_GT {
        ">"
    } else if op == BIN_LE {
        "<="
    } else if op == BIN_GE {
        ">="
    } else if op == BIN_AND {
        "&&"
    } else {
        "||"
    }
}

pub const PRIM_NONE: i64 = 0;
pub const PRIM_UNIT: i64 = 1;
pub const PRIM_RESULT: i64 = 2;
pub const PRIM_OPTION: i64 = 3;
pub const PRIM_DIV_ERROR: i64 = 4;
pub const PRIM_INDEX_ERROR: i64 = 5;

pub fn alloc_tyinfo(nodes: &mut Vec<i64>, key: i64, kind: i64, sym: i64, args: i64, elem: i64, len: i64) -> i64 {
    alloc_node(nodes, &[NODE_TYINFO, NO_FILE, NO_FILE, NO_FILE, key, kind, sym, args, elem, len])
}

pub fn find_tyinfo(nodes: &[i64], key: i64) -> i64 {
    if key < 0 || node_tag(nodes, key) != NODE_TYINFO || node_a(nodes, key) != key {
        return NONE;
    }
    key
}

pub fn tyinfo_is_linear(nodes: &[i64], key: i64) -> i64 {
    let row = find_tyinfo(nodes, key);
    if row == NONE {
        NONE
    } else {
        node_get(nodes, row, NODE_FILE)
    }
}

/// Whether a native container descriptor's type arguments include a linear
/// key (0 or 1, attached by the typechecker's linearity pass); NONE when
/// the flag was never attached.  Only meaningful for TYD_NATIVE rows.
pub fn tyinfo_has_linear_elems(nodes: &[i64], key: i64) -> i64 {
    let row = find_tyinfo(nodes, key);
    if row == NONE {
        NONE
    } else {
        node_get(nodes, row, NODE_START)
    }
}

pub fn tyinfo_builtin_kind(nodes: &[i64], key: i64) -> i64 {
    let row = find_tyinfo(nodes, key);
    if row == NONE {
        NONE
    } else {
        node_f(nodes, row)
    }
}

// Instance rows.  (tag=NODE_INST, a=fn slot, b=type-arg key list, c=return key,
// d=parameter key list, e=canonical mono key, f=symbol kind).  The source
// span belongs to the call that caused this instantiation; it is not a
// synthesized declaration, so it must never use NO_FILE.

pub fn alloc_instance(
    nodes: &mut Vec<i64>,
    span: (i64, i64, i64),
    data: (i64, i64, i64, i64, i64, i64),
) -> i64 {
    let (file, start, end) = span;
    let (fn_slot, args_list, result_key, param_keys_list, mono_key, sym_kind) = data;
    alloc_node(
        nodes,
        &[
            NODE_INST,
            file,
            start,
            end,
            fn_slot,
            args_list,
            result_key,
            param_keys_list,
            mono_key,
            sym_kind,
        ],
    )
}

pub fn inst_fn_of(nodes: &[i64], id: i64) -> i64 {
    node_a(nodes, id)
}

pub fn inst_args_of(nodes: &[i64], id: i64) -> i64 {
    node_b(nodes, id)
}

pub fn inst_set_args(nodes: &mut [i64], id: i64, list: i64) -> bool {
    node_set_b(nodes, id, list)
}

pub fn inst_ret_of(nodes: &[i64], id: i64) -> i64 {
    node_c(nodes, id)
}

pub fn inst_params_of(nodes: &[i64], id: i64) -> i64 {
    node_d(nodes, id)
}

pub fn inst_mono_of(nodes: &[i64], id: i64) -> i64 {
    node_e(nodes, id)
}

pub fn inst_set_ret(nodes: &mut [i64], id: i64, key: i64) -> bool {
    node_set_c(nodes, id, key)
}

pub fn inst_set_params(nodes: &mut [i64], id: i64, list: i64) -> bool {
    node_set_d(nodes, id, list)
}

pub fn inst_set_mono(nodes: &mut [i64], id: i64, key: i64) -> bool {
    node_set_e(nodes, id, key)
}

pub fn find_instance(nodes: &[i64], mono: i64) -> i64 {
    let mut idx = 0i64;
    while idx < nodes.len() as i64 / NODE_STRIDE {
        if node_tag(nodes, idx) == NODE_INST && node_e(nodes, idx) == mono {
            return idx;
        }
        idx += 1;
    }
    NONE
}

// Constant-value rows.  (tag=NODE_CONSTVAL, a=sym, b=value).

pub fn has_const_value(nodes: &[i64], sym: i64) -> bool {
    let mut idx = 0i64;
    while idx < nodes.len() as i64 / NODE_STRIDE {
        if node_tag(nodes, idx) == NODE_CONSTVAL && node_a(nodes, idx) == sym {
            return true;
        }
        idx += 1;
    }
    false
}

pub fn find_const_value(nodes: &[i64], sym: i64) -> i64 {
    let mut idx = 0i64;
    while idx < nodes.len() as i64 / NODE_STRIDE {
        if node_tag(nodes, idx) == NODE_CONSTVAL && node_a(nodes, idx) == sym {
            return node_b(nodes, idx);
        }
        idx += 1;
    }
    NONE
}

// Trait-dispatch rows.  (tag=NODE_TRAIT, a=call expr, b=method instance id,
// c=trait symbol, d=method name id, e=method fn node).  The method fn node
// is attached by the typechecker at dispatch-row creation so the borrow
// checker reads the signature directly instead of re-searching the trait's
// method list (Single-Fact Rule).

pub const NODE_TRAIT: i64 = 15;

pub fn trait_call_inst(nodes: &[i64], id: i64) -> i64 {
    node_b(nodes, id)
}

pub fn trait_call_trait(nodes: &[i64], id: i64) -> i64 {
    node_c(nodes, id)
}

pub fn trait_call_method(nodes: &[i64], id: i64) -> i64 {
    node_d(nodes, id)
}

pub fn trait_call_method_node(nodes: &[i64], id: i64) -> i64 {
    node_e(nodes, id)
}

pub fn alloc_trait_call(nodes: &mut Vec<i64>, expr: i64, inst: i64, trait_sym: i64, method: i64, fn_node: i64) -> i64 {
    alloc_node(nodes, &[NODE_TRAIT, NO_FILE, NO_FILE, NO_FILE, expr, inst, trait_sym, method, fn_node, NONE])
}

pub fn find_trait_call(nodes: &[i64], expr: i64) -> i64 {
    let mut idx = 0i64;
    while idx < nodes.len() as i64 / NODE_STRIDE {
        if node_tag(nodes, idx) == NODE_TRAIT && node_a(nodes, idx) == expr {
            return idx;
        }
        idx += 1;
    }
    NONE
}

// Variant-fact rows.  (tag=NODE_VARFACT, a=enum key, b=variant name id,
// c=variant symbol, d=declared-order tag).  The tag is assigned by the
// typechecker from the enum's declared variant order, once, and read by
// codegen instead of re-searching the enum's variant list (Single-Fact
// Rule).

pub const NODE_VARFACT: i64 = 16;

pub fn alloc_varfact(nodes: &mut Vec<i64>, key: i64, name: i64, sym: i64, tag: i64) -> i64 {
    alloc_node(nodes, &[NODE_VARFACT, NO_FILE, NO_FILE, NO_FILE, key, name, sym, tag, NONE, NONE])
}

pub fn find_varfact(nodes: &[i64], key: i64, name: i64) -> i64 {
    let mut idx = 0i64;
    while idx < nodes.len() as i64 / NODE_STRIDE {
        if node_tag(nodes, idx) == NODE_VARFACT && node_a(nodes, idx) == key && node_b(nodes, idx) == name {
            return node_c(nodes, idx);
        }
        idx += 1;
    }
    NONE
}

// The declared-order tag of `name` in the enum at `key`, or NONE.
pub fn varfact_index_of(nodes: &[i64], key: i64, name: i64) -> i64 {
    let mut idx = 0i64;
    while idx < nodes.len() as i64 / NODE_STRIDE {
        if node_tag(nodes, idx) == NODE_VARFACT && node_a(nodes, idx) == key && node_b(nodes, idx) == name {
            return node_d(nodes, idx);
        }
        idx += 1;
    }
    NONE
}

// Struct-field-fact rows.  (tag=NODE_FIELDKEY, a=struct key, b=field name
// id, c=substituted field key, d=declared-order index).  One row per
// (canonical struct key, field) pair, filled by the typechecker from the
// declared field types and the key's own type arguments; the borrow
// checker and codegen read these rows instead of re-walking ITEM_STRUCT
// lists and re-running generic substitution (Single-Fact Rule).

pub const NODE_FIELDKEY: i64 = 17;

// Resolver-owned tooling facts. These rows preserve the resolver's scope
// decisions after its transient lookup tables are gone, so editor tooling
// consumes name-resolution output instead of rebuilding a parallel scope
// walker.
//
// SCOPE_AT:      a=kind, b=source node, c=scope
// SCOPE_VISIBLE: a=kind, b=query scope, c=local name, d=symbol, e=namespace
// SCOPE_MEMBER:  a=kind, b=query scope, c=member scope, d=local name,
//                e=symbol, f=namespace
pub const NODE_SCOPEFACT: i64 = 18;
pub const SCOPE_AT: i64 = 0;
pub const SCOPE_VISIBLE: i64 = 1;
pub const SCOPE_MEMBER: i64 = 2;

pub fn alloc_scope_at(nodes: &mut Vec<i64>, source: i64, scope: i64) -> i64 {
    alloc_node(
        nodes,
        &[
            NODE_SCOPEFACT,
            NO_FILE,
            NO_FILE,
            NO_FILE,
            SCOPE_AT,
            source,
            scope,
            NONE,
            NONE,
            NONE,
        ],
    )
}

pub fn alloc_scope_visible(
    nodes: &mut Vec<i64>,
    scope: i64,
    name: i64,
    sym: i64,
    namespace: i64,
) -> i64 {
    alloc_node(
        nodes,
        &[
            NODE_SCOPEFACT,
            NO_FILE,
            NO_FILE,
            NO_FILE,
            SCOPE_VISIBLE,
            scope,
            name,
            sym,
            namespace,
            NONE,
        ],
    )
}

pub fn alloc_scope_member(
    nodes: &mut Vec<i64>,
    query: i64,
    member_scope: i64,
    name: i64,
    sym: i64,
    namespace: i64,
) -> i64 {
    alloc_node(
        nodes,
        &[
            NODE_SCOPEFACT,
            NO_FILE,
            NO_FILE,
            NO_FILE,
            SCOPE_MEMBER,
            query,
            member_scope,
            name,
            sym,
            namespace,
        ],
    )
}

// Typechecker-owned lexical-environment snapshots.  One row is attached
// for every visible local at a checked source node: a=source node, b=name,
// c=canonical type key, d=is_mut.  Completion reads these rows instead of
// reconstructing branch scopes from the raw AST.
pub const NODE_LOCALFACT: i64 = 19;

pub fn alloc_localfact(nodes: &mut Vec<i64>, source: i64, name: i64, key: i64, is_mut: i64) -> i64 {
    let file = node_file(nodes, source);
    let start = node_start(nodes, source);
    let end = node_end(nodes, source);
    alloc_node(
        nodes,
        &[
            NODE_LOCALFACT,
            file,
            start,
            end,
            source,
            name,
            key,
            is_mut,
            NONE,
            NONE,
        ],
    )
}

// Tail-safety-fact rows.  (tag=NODE_CALLFACT, a=call expr id, b=tail-safe
// flag, c=frame-local root name id or NONE).  The typechecker computes, for
// every call, whether any argument carries a reference rooted in the
// current function's frame — which is what would make LLVM's `tail` marker
// a false promise that the callee never touches the caller's frame — and
// attaches the result so codegen marks a call `tail` only when it is safe
// (Single-Fact Rule).  Slot `c` names the offending frame-local binding for
// the self-recursion rejection diagnostic; it is NONE when the call is
// tail-safe.

pub const NODE_CALLFACT: i64 = 21;

pub fn alloc_callfact(nodes: &mut Vec<i64>, call: i64, tail_safe: i64, root_name: i64) -> i64 {
    alloc_node(
        nodes,
        &[NODE_CALLFACT, NO_FILE, NO_FILE, NO_FILE, call, tail_safe, root_name, NONE, NONE, NONE],
    )
}

pub fn callfact_tail_safe_of(nodes: &[i64], call: i64) -> i64 {
    let mut idx = 0i64;
    while idx < nodes.len() as i64 / NODE_STRIDE {
        if node_tag(nodes, idx) == NODE_CALLFACT && node_a(nodes, idx) == call {
            return node_b(nodes, idx);
        }
        idx += 1;
    }
    0
}

pub fn callfact_root_name_of(nodes: &[i64], call: i64) -> i64 {
    let mut idx = 0i64;
    while idx < nodes.len() as i64 / NODE_STRIDE {
        if node_tag(nodes, idx) == NODE_CALLFACT && node_a(nodes, idx) == call {
            return node_c(nodes, idx);
        }
        idx += 1;
    }
    NONE
}

// Pattern-binding-fact rows.  (tag=NODE_PATFACT, a=pattern node, b=match
// scrutinee expr id).  The typechecker attaches one per binding pattern
// (PAT_BIND and the rest binder of PAT_ARRAY) so the tail-safety trace can
// resolve a match-arm binding's origin to the scrutinee it destructures
// without re-walking the arm list (Single-Fact Rule).

pub const NODE_PATFACT: i64 = 22;

pub fn alloc_patfact(nodes: &mut Vec<i64>, pat: i64, scrutinee: i64) -> i64 {
    alloc_node(nodes, &[NODE_PATFACT, NO_FILE, NO_FILE, NO_FILE, pat, scrutinee, NONE, NONE, NONE, NONE])
}

pub fn patfact_scrutinee_of(nodes: &[i64], pat: i64) -> i64 {
    let mut idx = 0i64;
    while idx < nodes.len() as i64 / NODE_STRIDE {
        if node_tag(nodes, idx) == NODE_PATFACT && node_a(nodes, idx) == pat {
            return node_b(nodes, idx);
        }
        idx += 1;
    }
    NONE
}

pub fn alloc_fieldkey(nodes: &mut Vec<i64>, key: i64, name: i64, fkey: i64, idx: i64) -> i64 {
    alloc_node(nodes, &[NODE_FIELDKEY, NO_FILE, NO_FILE, NO_FILE, key, name, fkey, idx, NONE, NONE])
}

pub fn find_fieldkey(nodes: &[i64], key: i64, name: i64) -> i64 {
    let mut idx = 0i64;
    while idx < nodes.len() as i64 / NODE_STRIDE {
        if node_tag(nodes, idx) == NODE_FIELDKEY && node_a(nodes, idx) == key && node_b(nodes, idx) == name {
            return idx;
        }
        idx += 1;
    }
    NONE
}

pub fn fieldkey_key_of(nodes: &[i64], row: i64) -> i64 {
    node_c(nodes, row)
}

pub fn fieldkey_idx_of(nodes: &[i64], row: i64) -> i64 {
    node_d(nodes, row)
}

fn list_eq(lists: &[Vec<i64>], a: i64, b: i64) -> bool {
    let na = list_len(lists, a);
    let nb = list_len(lists, b);
    if na != nb {
        return false;
    }
    let mut idx = 0i64;
    while idx < na {
        if list_get(lists, a, idx) != list_get(lists, b, idx) {
            return false;
        }
        idx += 1;
    }
    true
}

pub fn find_tyinfo_by(nodes: &[i64], lists: &[Vec<i64>], kind: i64, sym: i64, args: i64, elem: i64, len: i64) -> i64 {
    let mut idx = 0i64;
    while idx < nodes.len() as i64 / NODE_STRIDE {
        if node_tag(nodes, idx) == NODE_TYINFO
            && node_b(nodes, idx) == kind
            && node_c(nodes, idx) == sym
            && list_eq(lists, node_d(nodes, idx), args)
            && node_e(nodes, idx) == elem
            && node_f(nodes, idx) == len
        {
            return idx;
        }
        idx += 1;
    }
    NONE
}

pub fn canon_tyinfo(nodes: &mut Vec<i64>, lists: &mut [Vec<i64>], kind: i64, sym: i64, args: i64, elem: i64, len: i64) -> i64 {
    let existing = find_tyinfo_by(nodes, lists, kind, sym, args, elem, len);
    if existing != NONE {
        return node_a(nodes, existing);
    }
    let key = nodes.len() as i64 / NODE_STRIDE;
    alloc_tyinfo(nodes, key, kind, sym, args, elem, len);
    key
}

fn subst_list(nodes: &mut Vec<i64>, lists: &mut Vec<Vec<i64>>, list: i64, from: &[i64], to: &[i64]) -> i64 {
    let count = list_len(lists, list);
    if count == 0 {
        return list;
    }
    let fresh = alloc_list(lists);
    let mut changed = false;
    let mut idx = 0i64;
    while idx < count {
        let old = list_get(lists, list, idx);
        let new = subst_key(nodes, lists, old, from, to);
        list_push(lists, fresh, new);
        if new != old {
            changed = true;
        }
        idx += 1;
    }
    if changed {
        fresh
    } else {
        list
    }
}

pub fn subst_key(nodes: &mut Vec<i64>, lists: &mut Vec<Vec<i64>>, key: i64, from: &[i64], to: &[i64]) -> i64 {
    if key < 0 {
        return key;
    }
    let row = find_tyinfo(nodes, key);
    if row == NONE {
        return key;
    }
    let kind = node_b(nodes, row);
    let sym = node_c(nodes, row);
    if kind == TYD_PARAM {
        let mut idx = 0usize;
        loop {
            match from.get(idx) {
                Some(cand) => {
                    if *cand == key {
                        match to.get(idx) {
                            Some(repl) => return *repl,
                            None => return key,
                        }
                    }
                }
                None => return key,
            }
            idx += 1;
        }
    }
    let args = node_d(nodes, row);
    let elem = node_e(nodes, row);
    let len = node_f(nodes, row);
    let new_args = subst_list(nodes, lists, args, from, to);
    let new_elem = subst_key(nodes, lists, elem, from, to);
    if new_args == args && new_elem == elem {
        return key;
    }
    canon_tyinfo(nodes, lists, kind, sym, new_args, new_elem, len)
}

pub fn expr_diverges(nodes: &[i64], lists: &[Vec<i64>], expr: i64) -> i64 {
    if node_tag(nodes, expr) != NODE_EXPR || node_a(nodes, expr) != EXPR_MATCH {
        return 0;
    }
    let arms = node_c(nodes, expr);
    let count = list_len(lists, arms);
    if count == 0 {
        return 0;
    }
    let mut idx = 0i64;
    while idx < count {
        let arm = list_get(lists, arms, idx);
        if stmt_diverges(nodes, lists, node_b(nodes, arm)) == 0 {
            return 0;
        }
        idx += 1;
    }
    1
}

pub fn stmt_diverges(nodes: &[i64], lists: &[Vec<i64>], stmt: i64) -> i64 {
    if node_tag(nodes, stmt) != NODE_STMT {
        return 0;
    }
    let kind = node_a(nodes, stmt);
    if kind == STMT_RETURN || kind == STMT_BREAK || kind == STMT_CONTINUE {
        return 1;
    }
    if kind == STMT_EXPR {
        return expr_diverges(nodes, lists, node_b(nodes, stmt));
    }
    if kind == STMT_IF {
        if node_d(nodes, stmt) == NONE {
            return 0;
        }
        if stmt_list_diverges(nodes, lists, node_c(nodes, stmt)) == 0 {
            return 0;
        }
        return stmt_list_diverges(nodes, lists, node_d(nodes, stmt));
    }
    0
}

fn stmt_list_diverges(nodes: &[i64], lists: &[Vec<i64>], list: i64) -> i64 {
    let count = list_len(lists, list);
    if count == 0 {
        return 0;
    }
    stmt_diverges(nodes, lists, list_get(lists, list, count - 1))
}

pub fn list_len(lists: &[Vec<i64>], id: i64) -> i64 {
    match lists.get(id as usize) {
        Some(items) => items.len() as i64,
        None => 0,
    }
}

pub fn list_first(lists: &[Vec<i64>], id: i64) -> i64 {
    match lists.get(id as usize) {
        Some(items) => match items.first() {
            Some(value) => *value,
            None => NONE,
        },
        None => NONE,
    }
}

pub fn list_last(lists: &[Vec<i64>], id: i64) -> i64 {
    match lists.get(id as usize) {
        Some(items) => match items.last() {
            Some(value) => *value,
            None => NONE,
        },
        None => NONE,
    }
}

pub fn list_get(lists: &[Vec<i64>], id: i64, idx: i64) -> i64 {
    match lists.get(id as usize) {
        Some(items) => match items.get(idx as usize) {
            Some(value) => *value,
            None => NONE,
        },
        None => NONE,
    }
}

pub fn push_internal(errors: &mut Vec<Diag>, message: &str) {
    errors.push((message.to_string(), NO_FILE, 0, 0));
}

pub fn push_error(errors: &mut Vec<Diag>, message: &str, file: i64, start: i64, end: i64) {
    errors.push((message.to_string(), file, start, end));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn intern_dedups_names() {
        let mut names: Vec<String> = Vec::new();
        let a = intern(&mut names, "sum_to");
        let b = intern(&mut names, "sum_to");
        let c = intern(&mut names, "other");
        assert_eq!(a, b);
        assert_ne!(a, c);
        assert!(name_is(&names, a, "sum_to"));
    }

    #[test]
    fn node_roundtrip() {
        let mut nodes: Vec<i64> = Vec::new();
        let id = alloc_node(
            &mut nodes,
            &[NODE_EXPR, 0, 10, 20, EXPR_LIT, LIT_INT, 42, NONE, NONE, NONE],
        );
        assert_eq!(node_tag(&nodes, id), NODE_EXPR);
        assert_eq!(node_a(&nodes, id), EXPR_LIT);
        assert_eq!(node_b(&nodes, id), LIT_INT);
        assert_eq!(node_c(&nodes, id), 42);
        assert_eq!(expr_ty_of(&nodes, id), NONE);
        assert!(expr_set_ty(&mut nodes, id, 7));
        assert_eq!(expr_ty_of(&nodes, id), 7);
        assert_eq!(node_tag(&nodes, 999), NONE);
    }

    #[test]
    fn lists_grow() {
        let mut lists: Vec<Vec<i64>> = Vec::new();
        let list = alloc_list(&mut lists);
        assert!(list_push(&mut lists, list, 1));
        assert!(list_push(&mut lists, list, 2));
        match lists.get(list as usize) {
            Some(items) => assert_eq!(items.len(), 2),
            None => assert!(false),
        }
    }

    #[test]
    fn instance_row_preserves_call_fact_layout() {
        let mut nodes: Vec<i64> = Vec::new();
        let instance = alloc_instance(
            &mut nodes,
            (7, 11, 19),
            (23, 29, 31, 37, 41, SYM_NATIVE_FUN),
        );
        assert_eq!(node_tag(&nodes, instance), NODE_INST);
        assert_eq!(node_file(&nodes, instance), 7);
        assert_eq!(node_start(&nodes, instance), 11);
        assert_eq!(node_end(&nodes, instance), 19);
        assert_eq!(inst_fn_of(&nodes, instance), 23);
        assert_eq!(inst_args_of(&nodes, instance), 29);
        assert_eq!(inst_ret_of(&nodes, instance), 31);
        assert_eq!(inst_params_of(&nodes, instance), 37);
        assert_eq!(inst_mono_of(&nodes, instance), 41);
        assert_eq!(node_f(&nodes, instance), SYM_NATIVE_FUN);
    }

    #[test]
    fn canonical_type_key_is_descriptor_row() {
        let mut nodes: Vec<i64> = Vec::new();
        let mut lists: Vec<Vec<i64>> = Vec::new();
        let source = alloc_node(
            &mut nodes,
            &[NODE_EXPR, 0, 0, 1, EXPR_LIT, LIT_INT, 0, NONE, NONE, NONE],
        );
        assert_eq!(source, 0);

        let unknown = canon_tyinfo(&mut nodes, &mut lists, TYD_UNKNOWN, NONE, NONE, NONE, NONE);
        assert_eq!(unknown, 1);
        assert_eq!(find_tyinfo(&nodes, unknown), unknown);

        let later_source = alloc_node(
            &mut nodes,
            &[NODE_EXPR, 0, 1, 2, EXPR_LIT, LIT_INT, 1, NONE, NONE, NONE],
        );
        assert_eq!(later_source, 2);

        let builtin = canon_tyinfo(
            &mut nodes,
            &mut lists,
            TYD_BUILTIN,
            NONE,
            NONE,
            NONE,
            BUILTIN_I64,
        );
        assert_eq!(builtin, 3);
        assert_eq!(find_tyinfo(&nodes, builtin), builtin);
        assert_eq!(find_tyinfo(&nodes, source), NONE);

        let same_builtin = canon_tyinfo(
            &mut nodes,
            &mut lists,
            TYD_BUILTIN,
            NONE,
            NONE,
            NONE,
            BUILTIN_I64,
        );
        assert_eq!(same_builtin, builtin);
    }
}
