//! Flow-sensitive borrow, linearity, and container-state checking.
//!
//! A control-flow graph is built per function (`BLK_ENTRY`, `BLK_STMT`,
//! `BLK_JOIN`, `BLK_EXIT`) and walked to a fixpoint, so a fact holds on
//! every path rather than on the one the source happens to read like. Each
//! binding moves through a state lattice — `ST_UNBOUND`, `ST_LIVE`,
//! `ST_MOVED`, `ST_PARTIAL` — driven by the operations extracted from each
//! statement and expression (`OP_READ`, `OP_MOVE`, `OP_BORROW`,
//! `OP_BORROW_M`, `OP_ASSIGN`, `OP_BIND`, `OP_EXIT`, `OP_RET_REF`, and the
//! `OP_CONT_*` continuation variants covering `return`, `break`, and `try`
//! propagation). `apply_move` is the central transition.
//!
//! What it enforces: a linear value is consumed exactly once on every path
//! out of its scope, and a moved value can be neither moved nor *borrowed*
//! again — a borrow after the move reads a resource the move already
//! released, which is the use-after-free shape. No two `&mut` borrows of
//! one place are live at once, and no place is mutated through a shared
//! borrow or moved while borrowed. A struct holding one linear field among
//! several plain ones tracks that field individually, so moving it out
//! leaves the rest of the struct usable.
//!
//! A returned borrow whose origin cannot be pinned to one input is
//! rejected, which pushes the programmer to restructure the API rather than
//! annotate a lifetime. The per-function summary records which parameters a
//! returned borrow derives from, and an *empty* set means static: a string
//! literal or a `const` of reference type has no loan to trace and outlives
//! every caller, so one function can forward another's static result
//! without the borrow becoming untraceable at the call.
//!
//! Because a borrow fact can depend on a callee, the whole function set is
//! re-checked until no summary changes, bounded by a cap derived from the
//! function and parameter counts rather than by a fixed round limit.
//!
//! **Invariants:**
//! - Linearity is read here, never decided. It comes from the flag the
//!   typechecker attached to the canonical type descriptor; this file never
//!   infers a type of its own and never asks what a type is called.
//! - Every diagnostic and every attached `Note` carries a span the walk
//!   actually visited — a binding site, a path's last move, the
//!   per-predecessor exit states behind a join inconsistency.

use crate::ast::*;
use crate::typecheck::render_type_key;

const ST_UNBOUND: i64 = 0;
const ST_LIVE: i64 = 1;
const ST_MOVED: i64 = 2;
const ST_PARTIAL: i64 = 3;

const C_EMPTY: i64 = 0;
const C_MAY: i64 = 1;

const OP_READ: i64 = 0;
const OP_MOVE: i64 = 1;
const OP_BORROW: i64 = 2;
const OP_BORROW_M: i64 = 3;
const OP_ASSIGN: i64 = 4;
const OP_BIND: i64 = 5;
const OP_EXIT: i64 = 6;
const OP_RET_REF: i64 = 7;
const OP_CONT_EMPTY: i64 = 8;
const OP_CONT_MAY: i64 = 9;
const OP_CONT_FREE: i64 = 10;

const EX_RETURN: i64 = 0;
const EX_BREAK: i64 = 1;
const EX_TRY: i64 = 2;

const L_SHARED: i64 = 0;
const L_MUT: i64 = 1;

const IDX_DYN: i64 = -2;

const BLK_ENTRY: i64 = 0;
const BLK_STMT: i64 = 1;
const BLK_JOIN: i64 = 2;
const BLK_EXIT: i64 = 3;

const MODE_VALUE: i64 = 0;
const MODE_BORROW: i64 = 1;
const MODE_MUT: i64 = 2;

type F = (
    Vec<(i64, i64, i64, i64, i64, i64, i64)>,
    Vec<(i64, i64, i64)>,
    Vec<(i64, i64, i64)>,
    Vec<(i64, i64, i64, i64)>,
    Vec<(i64, i64, i64, i64, i64, i64, i64, i64, i64)>,
    Vec<Vec<i64>>,
    Vec<(i64, i64, i64, i64)>,
    Vec<Vec<i64>>,
    Vec<Vec<i64>>,
    Vec<Vec<i64>>,
    Vec<(i64, i64, i64)>,
);

type B = (
    Vec<(i64, i64)>,
    Vec<(i64, i64, i64)>,
    Vec<i64>,
    Vec<i64>,
    i64,
    i64,
    i64,
    i64,
    // (extraction result binding, container binding): the match consuming an
    // extraction result marks the container drained on its error arm.
    Vec<(i64, i64)>,
    // Bindings whose initializer is a native create call (vec_new / hash_map_new):
    // the container bound from them is provably empty.
    Vec<i64>,
);

type Ctx<'a> = (
    &'a mut Vec<String>,
    &'a mut Vec<i64>,
    &'a mut Vec<Vec<i64>>,
    &'a mut Vec<Diag>,

    &'a mut Vec<(i64, Vec<i64>)>,
    i64, // the interned "Err" variant name id of the seeded Result enum
    i64, // the interned "Ok" variant name id of the seeded Result enum
    // Secondary explanatory notes, each tied to the error it explains by
    // that error's index in the errors vec at push time.
    &'a mut Vec<Note>,
);

fn ref_origin(binding: i64) -> i64 {
    -1 - binding
}

fn is_ref_origin(entry: i64) -> bool {
    entry < 0
}

fn binding_at(f: &F, id: i64) -> (i64, i64, i64, i64, i64, i64, i64) {
    match f.0.get(id as usize) {
        Some(row) => *row,
        None => (NONE, NONE, NONE, NONE, NONE, NONE, NONE),
    }
}

fn loan_at(f: &F, id: i64) -> (i64, i64, i64, i64) {
    match f.3.get(id as usize) {
        Some(row) => *row,
        None => (NONE, NONE, 0, NONE),
    }
}

fn path_at(f: &F, id: i64) -> (i64, i64, i64) {
    match f.2.get(id as usize) {
        Some(row) => *row,
        None => (NONE, NONE, NONE),
    }
}

fn op_at(f: &F, id: i64) -> (i64, i64, i64, i64, i64, i64, i64, i64, i64) {
    match f.4.get(id as usize) {
        Some(row) => *row,
        None => (NONE, NONE, NONE, NONE, NONE, NONE, NONE, NONE, NONE),
    }
}

fn op_loans_at(f: &F, id: i64) -> Vec<i64> {
    match f.5.get(id as usize) {
        Some(list) => list.clone(),
        None => Vec::new(),
    }
}

fn block_at(f: &F, id: i64) -> (i64, i64, i64, i64) {
    match f.6.get(id as usize) {
        Some(row) => *row,
        None => (NONE, NONE, NONE, NONE),
    }
}

fn block_span_at(f: &F, id: i64) -> (i64, i64, i64) {
    match f.10.get(id as usize) {
        Some(span) => *span,
        None => (NO_FILE, 0, 0),
    }
}

fn succ_of(f: &F, block: i64) -> Vec<i64> {
    match f.8.get(block as usize) {
        Some(list) => list.clone(),
        None => Vec::new(),
    }
}

fn pred_of(f: &F, block: i64) -> Vec<i64> {
    match f.9.get(block as usize) {
        Some(list) => list.clone(),
        None => Vec::new(),
    }
}

fn list_has(list: &[i64], value: i64) -> bool {
    let mut idx = 0usize;
    while idx < list.len() {
        match list.get(idx) {
            Some(cell) => {
                if *cell == value {
                    return true;
                }
            }
            None => break,
        }
        idx += 1;
    }
    false
}

fn state_at(state: &[i64], path: i64) -> i64 {
    match state.get(path as usize) {
        Some(value) => *value,
        None => ST_UNBOUND,
    }
}

fn state_set(state: &mut [i64], path: i64, value: i64) {
    if path < 0 {
        return;
    }
    if let Some(cell) = state.get_mut(path as usize) {
        *cell = value;
    }
}

fn ty_kind_of(nodes: &[i64], key: i64) -> i64 {
    if key < 0 {
        return TYD_UNKNOWN;
    }
    let row = find_tyinfo(nodes, key);
    if row == NONE {
        TYD_UNKNOWN
    } else {
        node_b(nodes, row)
    }
}

fn ty_sym_of(nodes: &[i64], key: i64) -> i64 {
    let row = find_tyinfo(nodes, key);
    if row == NONE {
        NONE
    } else {
        node_c(nodes, row)
    }
}

fn ty_elem_of(nodes: &[i64], key: i64) -> i64 {
    let row = find_tyinfo(nodes, key);
    if row == NONE {
        NONE
    } else {
        node_e(nodes, row)
    }
}

fn is_ref_key(nodes: &[i64], key: i64) -> bool {
    let kind = ty_kind_of(nodes, key);
    kind == TYD_REF || kind == TYD_REF_MUT || kind == TYD_SLICE
}

fn is_linear_key(ctx: &mut Ctx, key: i64) -> i64 {
    if key == NONE {
        return 0;
    }
    if tyinfo_is_linear(ctx.1, key) == 1 {
        1
    } else {
        0
    }
}

fn key_args_of_key(nodes: &[i64], key: i64) -> i64 {
    let row = find_tyinfo(nodes, key);
    if row == NONE {
        NONE
    } else {
        node_d(nodes, row)
    }
}

// A native type holding type arguments is a container: it carries element
// types (Vec(T), HashMap(K, V)); a plain handle (Block, String) has none.
fn is_container_key(nodes: &[i64], key: i64) -> bool {
    ty_kind_of(nodes, key) == TYD_NATIVE && key_args_of_key(nodes, key) != NONE
}

// A container holds linear elements when its typechecker-attached flag says
// so; the flag covers every type argument (HashMap(K, V): the key counts
// too).  Read here instead of re-deriving linearity over the argument list
// (Single-Fact Rule).
fn container_has_linear_elem(ctx: &mut Ctx, key: i64) -> bool {
    is_container_key(ctx.1, key) && tyinfo_has_linear_elems(ctx.1, key) == 1
}

// The native opcode attached to `expr`'s monomorphic call instance, or
// NONE for non-native calls.  The callee path is deliberately ignored here:
// resolution and typechecking already attached the symbol and instance, so
// borrow checking consumes that fact instead of resolving the path again.
fn native_op_of(ctx: &mut Ctx, expr: i64) -> i64 {
    let inst = expr_sym_of(ctx.1, expr);
    if node_tag(ctx.1, inst) != NODE_INST {
        return NONE;
    }
    let fn_slot = inst_fn_of(ctx.1, inst);
    if node_tag(ctx.1, fn_slot) != NODE_SYM || node_a(ctx.1, fn_slot) != SYM_NATIVE_FUN {
        return NONE;
    }
    sym_native_op(ctx.1, fn_slot)
}

fn call_is_create(ctx: &mut Ctx, expr: i64) -> bool {
    if node_tag(ctx.1, expr) != NODE_EXPR || node_a(ctx.1, expr) != EXPR_CALL {
        return false;
    }
    let op = native_op_of(ctx, expr);
    op == NAT_VEC_NEW || op == NAT_HASH_MAP_NEW
}

// A literal `true` loop condition can never fall through: the loop's only
// exit is a `break`, so the exit block joins state from break paths only.
fn is_const_true(ctx: &Ctx, expr: i64) -> bool {
    node_tag(ctx.1, expr) == NODE_EXPR && node_a(ctx.1, expr) == EXPR_LIT && node_b(ctx.1, expr) == LIT_TRUE
}

// True when a returned reference is rooted in the program's static data
// rather than in anything the function or its caller owns: a string
// literal, or a constant of a reference type (which is one).
//
// Such a borrow has an origin — the binary's read-only data — and that
// origin outlives every caller, so there is no loan to trace and no
// lifetime question to answer. The returned-borrow rule (MANIFESTO
// principle 5) exists to reject a returned borrow whose origin *among the
// inputs* is unknown or ambiguous, which is a question about how long the
// caller's data lives. A static borrow has no input origin because it
// needs none, so it is not the ambiguous case the rule is about; treating
// it as one would make `fun name() &[U8] return "cinnabar" end`
// unwriteable, and returning a fixed message is one of the things string
// literals exist for.
//
// This can never be a `&mut`: a literal is not a place and a constant is
// not assignable, so nothing statically rooted can be borrowed mutably.
// Forwarding one is static too: a call whose callee's converged summary is
// an empty source set returns a borrow that derives from none of its
// arguments, which for a reference-returning function means it is static.
// The summary set only grows, so treating an empty set as static stays
// monotone and the call-graph fixpoint still converges.
fn static_rooted_ref(ctx: &Ctx, expr: i64) -> bool {
    if node_tag(ctx.1, expr) != NODE_EXPR {
        return false;
    }
    let kind = node_a(ctx.1, expr);
    if kind == EXPR_LIT {
        return node_b(ctx.1, expr) == LIT_STRING;
    }
    if kind == EXPR_PATH {
        let sym = expr_sym_of(ctx.1, expr);
        return sym != NONE && node_a(ctx.1, sym) == SYM_CONST;
    }
    if kind == EXPR_CALL {
        let inst = expr_sym_of(ctx.1, expr);
        if node_tag(ctx.1, inst) != NODE_INST {
            return false;
        }
        return match summary_of(ctx.4, inst_fn_of(ctx.1, inst)) {
            Some(positions) => positions.is_empty(),
            None => false,
        };
    }
    false
}

// The value of `expr` is a provably-empty container when it came from a
// native create call: a direct call, a path to a binding created by one
// (`b.9`), or a match whose scrutinee is such a value.  One
// implementation feeds both the pattern binds of a match on the value
// and the let-binding of the value itself, so the container state can
// never drift between the two consumers.
fn create_provenance(ctx: &mut Ctx, b: &B, expr: i64) -> i64 {
    if call_is_create(ctx, expr) {
        return 1;
    }
    let root = path_root_binding_of(ctx, b, expr);
    if root != NONE && list_has(&b.9, root) {
        return 1;
    }
    if node_tag(ctx.1, expr) == NODE_EXPR && node_a(ctx.1, expr) == EXPR_MATCH {
        return create_provenance(ctx, b, node_b(ctx.1, expr));
    }
    0
}

// The root binding of a call argument naming a container, unwrapping the
// `&`/`&mut` layer (`&mut v` and `v` both resolve to the binding of `v`).
fn container_binding_of(b: &B, ctx: &Ctx, arg: i64) -> i64 {
    if node_tag(ctx.1, arg) != NODE_EXPR {
        return NONE;
    }
    let kind = node_a(ctx.1, arg);
    if kind == EXPR_UNARY {
        let op = node_b(ctx.1, arg);
        if op == UN_REF || op == UN_REF_MUT {
            return container_binding_of(b, ctx, node_c(ctx.1, arg));
        }
        return NONE;
    }
    if kind == EXPR_PATH {
        let segs = node_b(ctx.1, arg);
        return lookup_name(b, list_first(ctx.2, segs));
    }
    NONE
}

fn extraction_container_of_binding(entries: &[(i64, i64)], binding: i64) -> i64 {
    let mut idx = 0usize;
    while idx < entries.len() {
        match entries.get(idx) {
            Some(pair) => {
                if pair.0 == binding {
                    return pair.1;
                }
            }
            None => break,
        }
        idx += 1;
    }
    NONE
}

// `b.8` ("this binding's value came from an extraction call on that
// container") and `b.9` ("this binding's value came from a native create
// call") are syntactic snapshots taken once, at the binding's own
// `STMT_LET`/pattern-bind site — they are consulted later (by
// `create_provenance` and `extraction_container_of_binding`) as if they were
// still true, with nothing keeping them in step with the container's actual
// state. A container that was empty when a fact was recorded is not empty
// forever: `let r = vec_pop(&mut v)` records `(r, v)` in `b.8`, and if `v` is
// then refilled (`vec_push(&mut v, elem)`) before a later `match r` reads
// `b.8`, the match's Err arm still (wrongly) proves `v` drained, and freeing
// `v` afterward leaks whatever the intervening push added. Likewise `val v =
// match vec_new()...` puts `v` in `b.9`, and a later `val w = v` after `v`
// was refilled would otherwise inherit "provably empty" through `b.9`
// unchanged.
//
// This is the one place either fact can go stale: any call that takes an
// *existing* container by `&mut` outside of an extraction native. Pruning
// both facts for that binding right here — rather than trying to make
// `create_provenance`/`extraction_container_of_binding` themselves
// flow-sensitive, which would need a full dataflow pass this single-walk
// build phase doesn't have yet — keeps every later syntactic lookup honest
// for the only way it can go wrong.
fn invalidate_container_facts(b: &mut B, binding: i64) {
    let mut idx = 0usize;
    while idx < b.9.len() {
        if b.9[idx] == binding {
            b.9.remove(idx);
        } else {
            idx += 1;
        }
    }
    let mut idx = 0usize;
    while idx < b.8.len() {
        if b.8[idx].1 == binding {
            b.8.remove(idx);
        } else {
            idx += 1;
        }
    }
}

// Passing a linear-element container by &mut may fill it (an insertion native
// or any callee could push), so the container state rises to MayContain.
fn fill_container_if_mut_arg(f: &mut F, b: &mut B, ctx: &mut Ctx, arg: i64) {
    let binding = container_binding_of(b, ctx, arg);
    if binding < 0 {
        return;
    }
    let row = binding_at(f, binding);
    if container_has_linear_elem(ctx, row.1) {
        emit_op(f, OP_CONT_MAY, binding, NONE, (0, 0, 0), expr_span(ctx.1, arg));
        invalidate_container_facts(b, binding);
    }
}

// The arm that stands for the error variant of an extraction match, read
// from attached facts only (Single-Fact Rule): the pattern's resolved
// variant symbol (`pat_sym_of`) is compared against the scrutinee enum's
// error-variant symbol looked up in the typechecker's variant-fact table.
// A binding arm is the error arm exactly when it is the second arm of a
// 2-arm match whose first arm matches the Ok variant — exhaustiveness then
// forces the binding to cover Err.  A bare binding with no Ok arm covers
// both variants and proves nothing, so it is not the error arm.
fn arm_is_result_err(ctx: &mut Ctx, scrut_key: i64, pat: i64, arms: i64, idx: i64) -> bool {
    if node_tag(ctx.1, pat) != NODE_PAT {
        return false;
    }
    if ty_kind_of(ctx.1, scrut_key) != TYD_ENUM {
        return false;
    }
    let kind = node_a(ctx.1, pat);
    if kind == PAT_VARIANT {
        let pat_sym = pat_sym_of(ctx.1, pat);
        let err_sym = find_varfact(ctx.1, scrut_key, ctx.5);
        pat_sym != NONE && pat_sym == err_sym
    } else if kind == PAT_BIND {
        if idx != 1 || list_len(ctx.2, arms) != 2 {
            return false;
        }
        let first_pat = node_a(ctx.1, list_get(ctx.2, arms, 0));
        if node_tag(ctx.1, first_pat) != NODE_PAT || node_a(ctx.1, first_pat) != PAT_VARIANT {
            return false;
        }
        let ok_sym = find_varfact(ctx.1, scrut_key, ctx.6);
        let first_sym = pat_sym_of(ctx.1, first_pat);
        first_sym != NONE && first_sym == ok_sym
    } else {
        false
    }
}

fn cur(b: &B) -> i64 {
    b.4
}

fn close_current(f: &mut F, b: &mut B) {
    let id = b.4;
    if id < 0 {
        return;
    }
    if let Some(row) = f.6.get_mut(id as usize) {
        row.3 = f.4.len() as i64;
    }
}

fn new_block(f: &mut F, b: &mut B, kind: i64, stmt: i64, span: (i64, i64, i64)) -> i64 {
    close_current(f, b);
    let id = f.6.len() as i64;
    let first_op = f.4.len() as i64;
    f.6.push((kind, stmt, first_op, first_op));
    f.7.push(b.2.clone());
    f.8.push(Vec::new());
    f.9.push(Vec::new());
    f.10.push(span);
    b.4 = id;
    id
}

fn resume(f: &mut F, b: &mut B, block: i64) {
    close_current(f, b);
    if let Some(row) = f.6.get_mut(block as usize) {
        row.2 = f.4.len() as i64;
    }
    b.4 = block;
}

fn add_edge(f: &mut F, from: i64, to: i64) {
    if from < 0 || to < 0 {
        return;
    }
    if let Some(list) = f.8.get_mut(from as usize) {
        list.push(to);
    }
    if let Some(list) = f.9.get_mut(to as usize) {
        list.push(from);
    }
}

fn block_op_end(f: &F, block: i64) -> i64 {
    let row = block_at(f, block);
    let mut end = row.3;
    if end < row.2 {
        end = row.2;
    }
    end
}

fn emit_op(f: &mut F, kind: i64, binding: i64, path: i64, aux: (i64, i64, i64), span: (i64, i64, i64)) -> i64 {
    f.4.push((kind, binding, path, aux.0, aux.1, aux.2, span.0, span.1, span.2));
    f.5.push(Vec::new());
    f.4.len() as i64 - 1
}

fn set_op_loans(f: &mut F, op: i64, loans: &[i64]) {
    if let Some(list) = f.5.get_mut(op as usize) {
        list.clear();
        let mut idx = 0usize;
        while idx < loans.len() {
            match loans.get(idx) {
                Some(loan) => list.push(*loan),
                None => break,
            }
            idx += 1;
        }
    }
}

fn alloc_loan(f: &mut F, owner: i64, kind: i64, synthetic: i64, index_key: i64) -> i64 {
    let id = f.3.len() as i64;
    f.3.push((owner, kind, synthetic, index_key));
    id
}

fn root_path_of(f: &F, binding: i64) -> i64 {
    binding_at(f, binding).6
}

fn find_child(f: &F, path: i64, field: i64) -> i64 {
    let mut idx = 0usize;
    while idx < f.2.len() {
        let row = path_at(f, idx as i64);
        if row.0 == path && row.1 == field {
            return idx as i64;
        }
        idx += 1;
    }
    NONE
}

fn child_path(f: &mut F, path: i64, field: i64) -> i64 {
    let existing = find_child(f, path, field);
    if existing != NONE {
        return existing;
    }
    let root = path_at(f, path).2;
    let id = f.2.len() as i64;
    f.2.push((path, field, root));
    id
}

fn materialize_linear_subpaths(f: &mut F, ctx: &mut Ctx, key: i64, path: i64) {
    if key == NONE || path < 0 {
        return;
    }
    let sym = ty_sym_of(ctx.1, key);
    if sym == NONE {
        return;
    }
    let decl = node_c(ctx.1, sym);
    if decl == NONE || node_a(ctx.1, decl) != ITEM_STRUCT {
        return;
    }
    let fields = node_e(ctx.1, decl);
    let count = list_len(ctx.2, fields);
    let mut idx = 0i64;
    while idx < count {
        let fnode = list_get(ctx.2, fields, idx);
        let field = node_a(ctx.1, fnode);
        let fkey = field_key_of(ctx, key, field);
        if is_linear_key(ctx, fkey) == 1 {
            let child = child_path(f, path, field);
            materialize_linear_subpaths(f, ctx, fkey, child);
        }
        idx += 1;
    }
}

fn bind_state_live(f: &F, state: &mut [i64], binding: i64) {
    let root = root_path_of(f, binding);
    if root < 0 {
        return;
    }
    state_set(state, root, ST_LIVE);
    let mut idx = 0usize;
    while idx < f.2.len() {
        if path_at(f, idx as i64).2 == root {
            state_set(state, idx as i64, ST_LIVE);
        }
        idx += 1;
    }
}

fn is_root_path(f: &F, path: i64) -> bool {
    path_at(f, path).0 == NONE
}

fn bind_var(f: &mut F, b: &mut B, ctx: &mut Ctx, name: i64, key: i64, flags: (i64, i64, i64, i64), span: (i64, i64, i64)) -> i64 {
    let id = f.0.len() as i64;
    let root = if flags.0 == 1 {
        let r = f.2.len() as i64;
        f.2.push((NONE, NONE, r));
        materialize_linear_subpaths(f, ctx, key, r);
        r
    } else if flags.1 == 1 && flags.2 == 1 && ty_kind_of(ctx.1, key) == TYD_REF_MUT && is_linear_key(ctx, ty_elem_of(ctx.1, key)) == 1 {
        let r = f.2.len() as i64;
        f.2.push((NONE, NONE, r));
        materialize_linear_subpaths(f, ctx, ty_elem_of(ctx.1, key), r);
        r
    } else {
        NONE
    };
    f.0.push((name, key, flags.0, flags.1, flags.2, flags.3, root));
    f.1.push(span);
    b.2.push(id);
    b.0.push((name, id));
    id
}

fn stmt_span(nodes: &[i64], stmt: i64) -> (i64, i64, i64) {
    (node_file(nodes, stmt), node_start(nodes, stmt), node_end(nodes, stmt))
}

fn expr_span(nodes: &[i64], expr: i64) -> (i64, i64, i64) {
    (node_file(nodes, expr), node_start(nodes, expr), node_end(nodes, expr))
}

fn build_fn(f: &mut F, b: &mut B, ctx: &mut Ctx, fn_node: i64) -> bool {
    let body = node_f(ctx.1, fn_node);
    if body == NONE {
        return false;
    }
    let ret = ty_key_of(ctx.1, node_d(ctx.1, fn_node));
    let params = node_c(ctx.1, fn_node);
    let count = list_len(ctx.2, params);
    let fn_span = (node_file(ctx.1, fn_node), node_start(ctx.1, fn_node), node_end(ctx.1, fn_node));

    let entry = new_block(f, b, BLK_ENTRY, NONE, fn_span);
    let mut idx = 0i64;
    while idx < count {
        let param = list_get(ctx.2, params, idx);
        let name = node_a(ctx.1, param);
        let key = ty_key_of(ctx.1, node_b(ctx.1, param));
        let span = stmt_span(ctx.1, param);
        let flags = (is_linear_key(ctx, key), if is_ref_key(ctx.1, key) { 1 } else { 0 }, 1, 0);
        let binding = bind_var(f, b, ctx, name, key, flags, span);
        if flags.1 == 1 {
            let op = emit_op(f, OP_BIND, binding, NONE, (1, 1, 0), span);
            let loan = alloc_loan(f, binding, if ty_kind_of(ctx.1, key) == TYD_REF_MUT { L_MUT } else { L_SHARED }, 1, NONE);
            let loans = [loan];
            set_op_loans(f, op, &loans);
        } else {
            emit_op(f, OP_BIND, binding, NONE, (0, 1, 0), span);
        }
        // A by-value container parameter arrives with unknown provenance and
        // may hold linear elements, so it starts MayContain; only a drain
        // inside the callee can prove it empty before a free.
        if flags.1 == 0 && container_has_linear_elem(ctx, key) {
            emit_op(f, OP_CONT_MAY, binding, NONE, (0, 0, 0), span);
        }
        idx += 1;
    }

    let exit = new_block(f, b, BLK_EXIT, NONE, fn_span);
    b.5 = exit;
    emit_op(f, OP_EXIT, NONE, NONE, (0, EX_RETURN, 0), fn_span);

    let entry_of_body = build_list(f, b, ctx, body, exit, ret, &mut Vec::new());
    add_edge(f, entry, entry_of_body);

    close_current(f, b);
    let mut all: Vec<i64> = Vec::new();
    let mut bidx = 0usize;
    while bidx < f.0.len() {
        all.push(bidx as i64);
        bidx += 1;
    }
    if let Some(list) = f.7.get_mut(exit as usize) {
        list.clear();
        let mut j = 0usize;
        while j < all.len() {
            match all.get(j) {
                Some(v) => list.push(*v),
                None => break,
            }
            j += 1;
        }
    }
    true
}

fn build_list(f: &mut F, b: &mut B, ctx: &mut Ctx, list: i64, out: i64, ret: i64, prod: &mut Vec<i64>) -> i64 {
    let scope_start = b.2.len();
    let name_start = b.0.len();
    let cont_start = b.8.len();
    let empty_start = b.9.len();
    let count = list_len(ctx.2, list);
    if count == 0 {
        let stub = new_block(f, b, BLK_JOIN, NONE, block_span_at(f, out));
        if let Some(row) = f.6.get_mut(stub as usize) {
            row.3 = f.4.len() as i64;
        }
        add_edge(f, stub, out);
        return stub;
    }
    let mut entry = NONE;
    let mut after = NONE;
    let mut production: Vec<i64> = Vec::new();
    let mut fell = true;
    let mut idx = 0i64;
    while idx < count {
        let stmt = list_get(ctx.2, list, idx);
        b.3.clear();
        let (ent, aft, stmt_prod) = build_stmt(f, b, ctx, stmt, out, ret);
        if entry == NONE {
            entry = ent;
        }
        if fell && after != NONE {
            add_edge(f, after, ent);
        }
        if fell && aft != NONE {
            after = aft;
            production = stmt_prod;
        }
        if aft == NONE {
            fell = false;
        }
        idx += 1;
    }
    if fell && after != NONE {
        add_edge(f, after, out);
    }
    append_prod_unique(prod, &production);
    while b.2.len() > scope_start {
        b.2.pop();
    }
    while b.0.len() > name_start {
        b.0.pop();
    }
    while b.8.len() > cont_start {
        b.8.pop();
    }
    while b.9.len() > empty_start {
        b.9.pop();
    }
    entry
}

fn build_stmt(f: &mut F, b: &mut B, ctx: &mut Ctx, stmt: i64, out: i64, ret: i64) -> (i64, i64, Vec<i64>) {
    let kind = node_a(ctx.1, stmt);
    let span = stmt_span(ctx.1, stmt);
    if kind == STMT_LET {
        let block = new_block(f, b, BLK_STMT, stmt, span);
        let name = node_c(ctx.1, stmt);
        let is_mut = node_b(ctx.1, stmt);
        let init = node_e(ctx.1, stmt);
        let has_init = if init == NONE { 0 } else { 1 };
        let binding_key = stmt_ty_of(ctx.1, stmt);
        let mut prod: Vec<i64> = Vec::new();
        let cont = if has_init == 1 {
            expr_effects(f, b, ctx, init, MODE_VALUE, ret, &mut prod)
        } else {
            block
        };
        let flags = (is_linear_key(ctx, binding_key), if is_ref_key(ctx.1, binding_key) { 1 } else { 0 }, 0, is_mut);
        let binding = bind_var(f, b, ctx, name, binding_key, flags, span);
        let op = emit_op(f, OP_BIND, binding, NONE, (flags.1, has_init, 0), span);
        // A struct/array literal whose field initialisers borrow keeps those
        // loans against the new binding, so a later borrow of `s.f` resolves
        // back to the underlying owner instead of being dropped.
        if has_init == 1 && (flags.1 == 1 || !prod.is_empty()) {
            set_op_loans(f, op, &prod);
        }
        if has_init == 1 && create_provenance(ctx, b, init) == 1 {
            b.9.push(binding);
        }
        if has_init == 1 && node_a(ctx.1, init) == EXPR_CALL && node_c(ctx.1, init) != NONE {
            let container = lookup_name(b, node_c(ctx.1, init));
            if container >= 0 {
                b.8.push((binding, container));
            }
        }
        // A container binding is empty only when its value has empty
        // provenance (a native create call, or a match on one); any other
        // provenance (a user function, an arbitrary match) may carry
        // linear elements.
        if container_has_linear_elem(ctx, binding_key) {
            if has_init == 1 && create_provenance(ctx, b, init) == 1 {
                emit_op(f, OP_CONT_EMPTY, binding, NONE, (0, 0, 0), span);
            } else {
                emit_op(f, OP_CONT_MAY, binding, NONE, (0, 0, 0), span);
            }
        }
        return (block, cont, prod);
    }
    if kind == STMT_ASSIGN {
        let block = new_block(f, b, BLK_STMT, stmt, span);
        let target = node_b(ctx.1, stmt);
        let value = node_c(ctx.1, stmt);
        let mut prod: Vec<i64> = Vec::new();
        let cont = expr_effects(f, b, ctx, value, MODE_VALUE, ret, &mut prod);
        let (binding, path, tkind, owner) = assign_target_of(f, b, ctx, target);
        let is_ref = if tkind == 0 && binding >= 0 { binding_at(f, binding).3 } else { 0 };
        let op = emit_op(f, OP_ASSIGN, binding, path, (is_ref, tkind, owner), span);
        if tkind == 0 && (is_ref == 1 || !prod.is_empty()) {
            set_op_loans(f, op, &prod);
        }
        return (block, cont, Vec::new());
    }
    if kind == STMT_WHILE {
        let block = new_block(f, b, BLK_STMT, stmt, span);
        let cond = node_b(ctx.1, stmt);
        let body = node_c(ctx.1, stmt);
        let join = new_block(f, b, BLK_JOIN, NONE, span);
        // `new_block` makes the block it creates current, so the condition
        // built below would otherwise emit into the loop-exit join and
        // `expr_effects` would hand back the join as `cont`.  That made the
        // exit block the branch point, gave it a self-edge, and -- because
        // `break` targets the join -- fed every break's exit state back into
        // the loop body.  A bare `flag` or any comparison forms no block of
        // its own, so that was the ordinary case, not an edge case.  The join
        // is still created first: `break` and `continue` need it as their
        // target while the condition is being built.
        resume(f, b, block);
        let scope_start = b.2.len() as i64;
        b.1.push((block, join, scope_start));
        let cont = expr_effects(f, b, ctx, cond, MODE_VALUE, ret, &mut Vec::new());
        let const_true = is_const_true(ctx, cond);
        let body_entry = build_list(f, b, ctx, body, block, ret, &mut Vec::new());
        b.1.pop();
        // A condition that emitted no block of its own leaves `cont` as the
        // header, which is already where control arrives.
        if cont != block {
            add_edge(f, block, cont);
        }
        add_edge(f, cont, body_entry);
        // A literal-true condition has no false path: the loop exits only via
        // `break`, so the join merges only break-path state.  Routing the
        // condition into the join would smuggle the pre-loop state (container
        // still C_MAY, value still LIVE) onto the exit path, defeating the
        // `while true` drain proof.  The join-to-out edge belongs to the
        // enclosing list's sequencing (build_list), not here, so a mid-list
        // loop cannot feed its exit state past the statements that follow it.
        if !const_true {
            add_edge(f, cont, join);
        }
        return (block, join, Vec::new());
    }
    if kind == STMT_IF {
        let block = new_block(f, b, BLK_STMT, stmt, span);
        let cond = node_b(ctx.1, stmt);
        let then_list = node_c(ctx.1, stmt);
        let else_list = node_d(ctx.1, stmt);
        // The condition is built before the join exists.  `new_block` makes
        // the block it creates current, and a condition that needs no block of
        // its own (a bare `flag`) returns whatever is current -- so creating
        // the join first made `cont` *be* the join.  Every branch edge then
        // hung off the join: it gained the arms as successors and as
        // predecessors, so each arm's entry merged the other arm's exit, and a
        // value consumed on every arm was reported both as moved twice and as
        // consumed on only some paths.  The `while` lowering above had the
        // same hazard and is fixed the same way, by keeping the header current
        // while the condition is built.
        let cont = expr_effects(f, b, ctx, cond, MODE_VALUE, ret, &mut Vec::new());
        let join = new_block(f, b, BLK_JOIN, NONE, span);
        // A condition that emitted no block of its own leaves `cont` as the
        // statement block itself, which is already where control arrives.
        if cont != block {
            add_edge(f, block, cont);
        }
        let then_entry = build_list(f, b, ctx, then_list, join, ret, &mut Vec::new());
        add_edge(f, cont, then_entry);
        if else_list != NONE {
            let else_entry = build_list(f, b, ctx, else_list, join, ret, &mut Vec::new());
            add_edge(f, cont, else_entry);
        } else {
            add_edge(f, cont, join);
        }
        // The join-to-out edge belongs to the enclosing list's sequencing
        // (build_list): an if mid-list must not feed its exit state past the
        // statements that follow it, or a linear value consumed after the if
        // would be falsely reported live at the function exit.
        return (block, join, Vec::new());
    }
    if kind == STMT_RETURN {
        let block = new_block(f, b, BLK_STMT, stmt, span);
        let value = node_b(ctx.1, stmt);
        if value == NONE {
            emit_op(f, OP_EXIT, NONE, NONE, (0, EX_RETURN, 0), span);
            return (block, NONE, Vec::new());
        }
        let mut prod: Vec<i64> = Vec::new();
        expr_effects(f, b, ctx, value, MODE_VALUE, ret, &mut prod);
        // The returned-borrow obligation must apply whenever the *declared
        // return type* can carry a reference anywhere in its structure, not
        // only when it is bare `&T`/`&mut T`/`&[T]`: a function returning
        // `Result(&T, E)` or a struct with a reference field can return a
        // dangling borrow of a local exactly the way a bare `&T`-returning
        // one can, and `prod` already carries the right origin regardless of
        // the wrapping shape (struct/variant construction propagates its
        // arguments' own prod).
        let mut seen: Vec<i64> = Vec::new();
        if crate::typecheck::type_contains_ref(ctx.1, ctx.2, ret, &mut seen)
            && !static_rooted_ref(ctx, value)
        {
            let op = emit_op(f, OP_RET_REF, NONE, NONE, (0, 0, 0), span);
            set_op_loans(f, op, &prod);
        }
        emit_op(f, OP_EXIT, NONE, NONE, (0, EX_RETURN, 0), span);
        return (block, NONE, Vec::new());
    }
    if kind == STMT_BREAK {
        let block = new_block(f, b, BLK_STMT, stmt, span);
        let loop_scope = match b.1.last() {
            Some(row) => row.2,
            None => 0,
        };
        let join = match b.1.last() {
            Some(row) => row.1,
            None => out,
        };
        emit_op(f, OP_EXIT, NONE, NONE, (loop_scope, EX_BREAK, 0), span);
        add_edge(f, block, join);
        return (block, NONE, Vec::new());
    }
    if kind == STMT_CONTINUE {
        let block = new_block(f, b, BLK_STMT, stmt, span);
        let header = match b.1.last() {
            Some(row) => row.0,
            None => out,
        };
        add_edge(f, block, header);
        return (block, NONE, Vec::new());
    }
    let block = new_block(f, b, BLK_STMT, stmt, span);
    let expr = node_b(ctx.1, stmt);
    let mut prod: Vec<i64> = Vec::new();
    let cont = expr_effects(f, b, ctx, expr, MODE_VALUE, ret, &mut prod);
    (block, cont, prod)
}

fn lookup_name(b: &B, name: i64) -> i64 {
    let mut depth = b.0.len();
    while depth > 0 {
        depth -= 1;
        match b.0.get(depth) {
            Some(pair) => {
                if pair.0 == name {
                    return pair.1;
                }
            }
            None => break,
        }
    }
    NONE
}

fn expr_effects(f: &mut F, b: &mut B, ctx: &mut Ctx, expr: i64, mode: i64, ret: i64, prod: &mut Vec<i64>) -> i64 {
    if node_tag(ctx.1, expr) != NODE_EXPR {
        return cur(b);
    }
    let kind = node_a(ctx.1, expr);
    if kind == EXPR_LIT {
        return cur(b);
    }
    if kind == EXPR_PATH {
        return path_effects(f, b, ctx, expr, mode, prod);
    }
    if kind == EXPR_UNARY {
        return unary_effects(f, b, ctx, expr, ret, prod);
    }
    if kind == EXPR_BINARY {
        return binary_effects(f, b, ctx, expr, ret, prod);
    }
    if kind == EXPR_CALL {
        return call_effects(f, b, ctx, expr, ret, prod);
    }
    if kind == EXPR_STRUCT_LIT {
        return struct_effects(f, b, ctx, expr, ret, prod);
    }
    if kind == EXPR_ARRAY {
        return array_effects(f, b, ctx, expr, ret, prod);
    }
    if kind == EXPR_MATCH {
        return match_effects(f, b, ctx, expr, ret, prod);
    }
    if kind == EXPR_TRY {
        return try_effects(f, b, ctx, expr, ret, prod);
    }
    if kind == EXPR_INDEX {
        let base = node_b(ctx.1, expr);
        let index = node_c(ctx.1, expr);
        let base_kind = node_a(ctx.1, base);
        let level_key = index_key_of_literal(ctx, index);
        let level_list = if level_key == IDX_DYN {
            IDX_DYN
        } else {
            let list = alloc_list(ctx.2);
            list_push(ctx.2, list, level_key);
            list
        };
        let saved_op = b.6;
        let saved_idx = b.7;
        b.7 = level_list;
        let cont = expr_effects(f, b, ctx, base, mode, ret, prod);
        b.7 = saved_idx;
        if b.6 != saved_op
            && !prod.is_empty()
            && (base_kind == EXPR_PATH || base_kind == EXPR_FIELD_ACCESS || base_kind == EXPR_INDEX)
        {
            let mut stamped: i64 = NONE;
            let mut pi = 0usize;
            while pi < prod.len() {
                match prod.get(pi) {
                    Some(entry) => {
                        if *entry >= 0 {
                            stamped = extend_loan_index(f, ctx, *entry, level_key);
                        }
                    }
                    None => break,
                }
                pi += 1;
            }
            if stamped != NONE {
                stamp_op_index(f, b.6, stamped);
            }
        }
        expr_effects(f, b, ctx, index, MODE_VALUE, ret, &mut Vec::new());
        b.6 = saved_op;
        return cont;
    }
    if kind == EXPR_FIELD_ACCESS {
        let base = node_b(ctx.1, expr);
        let base_key = expr_ty_of(ctx.1, base);
        let base_kind = ty_kind_of(ctx.1, base_key);
        let base_mode = if base_kind == TYD_REF || base_kind == TYD_REF_MUT {
            if mode == MODE_VALUE {
                MODE_BORROW
            } else {
                mode
            }
        } else {
            mode
        };
        let mut base_prod: Vec<i64> = Vec::new();
        let cont = expr_effects(f, b, ctx, base, base_mode, ret, &mut base_prod);
        if mode == MODE_VALUE && (base_kind == TYD_REF || base_kind == TYD_REF_MUT) {
            prod.clear();
            append_list_unique(prod, &base_prod);
        }
        return cont;
    }
    cur(b)
}

fn path_effects(f: &mut F, b: &mut B, ctx: &mut Ctx, expr: i64, mode: i64, prod: &mut Vec<i64>) -> i64 {
    let segs = node_b(ctx.1, expr);
    let first = list_first(ctx.2, segs);
    let binding = lookup_name(b, first);
    if binding == NONE {
        return cur(b);
    }
    let row = binding_at(f, binding);
    let is_lin = row.2;
    let seg_count = list_len(ctx.2, segs);
    let span = expr_span(ctx.1, expr);

    if seg_count == 1 {
        if mode == MODE_BORROW || mode == MODE_MUT {
            return borrow_binding(f, b, ctx, binding, mode, span, prod);
        }
        if is_lin == 1 {
            check_pending_conflict(f, b, ctx, binding, MODE_VALUE, span);
            emit_op(f, OP_MOVE, binding, row.6, (0, 0, 0), span);
            return cur(b);
        }
        emit_op(f, OP_READ, binding, NONE, (0, 0, 0), span);
        if is_ref_key(ctx.1, row.1) {
            prod.clear();
            prod.push(ref_origin(binding));
        }
        return cur(b);
    }

    walk_field_chain(f, b, ctx, expr, binding, mode, prod);
    cur(b)
}

fn borrow_binding(f: &mut F, b: &mut B, ctx: &mut Ctx, binding: i64, mode: i64, span: (i64, i64, i64), prod: &mut Vec<i64>) -> i64 {
    let row = binding_at(f, binding);
    let op_kind = if mode == MODE_MUT { OP_BORROW_M } else { OP_BORROW };
    let loan_kind = if mode == MODE_MUT { L_MUT } else { L_SHARED };
    prod.clear();
    if row.3 == 1 {
        let op = emit_op(f, op_kind, binding, NONE, (0, 0, NONE), span);
        check_pending_conflict(f, b, ctx, binding, mode, span);
        b.6 = op;
        let loan = alloc_loan(f, binding, loan_kind, 0, NONE);
        b.3.push(loan);
        prod.push(ref_origin(binding));
        return cur(b);
    }
    check_pending_conflict(f, b, ctx, binding, mode, span);
    let op = emit_op(f, op_kind, binding, row.6, (0, 0, NONE), span);
    b.6 = op;
    let loan = alloc_loan(f, binding, loan_kind, 0, NONE);
    b.3.push(loan);
    prod.push(loan);
    cur(b)
}

fn check_pending_conflict(f: &mut F, b: &mut B, ctx: &mut Ctx, binding: i64, mode: i64, span: (i64, i64, i64)) {
    let new_key = b.7;
    let mut idx = 0usize;
    while idx < b.3.len() {
        let loan_id = match b.3.get(idx) {
            Some(id) => *id,
            None => break,
        };
        let loan = loan_at(f, loan_id);
        if loan.0 == binding && index_keys_conflict(ctx, new_key, loan.3) {
            let conflicting = if mode == MODE_BORROW {
                loan.1 == L_MUT
            } else {
                true
            };
            if conflicting {
                let row = binding_at(f, binding);
                let name = format!("{}{}", name_text(ctx.0, row.0), index_suffix(ctx, new_key));
                if mode == MODE_VALUE {
                    push_error(ctx.3, &format!("cannot move '{}' while it is borrowed in the same expression", name), span.0, span.1, span.2);
                } else if mode == MODE_MUT {
                    if loan.1 == L_SHARED {
                        push_error(ctx.3, &format!("cannot mutably borrow '{}' while it is shared-borrowed in the same expression", name), span.0, span.1, span.2);
                    } else {
                        push_error(ctx.3, &format!("cannot mutably borrow '{}' twice in the same expression", name), span.0, span.1, span.2);
                    }
                } else {
                    push_error(ctx.3, &format!("cannot borrow '{}' while it is mutably borrowed in the same expression", name), span.0, span.1, span.2);
                }
            }
        }
        idx += 1;
    }
}

fn index_key_of_literal(ctx: &Ctx, expr: i64) -> i64 {
    if node_tag(ctx.1, expr) == NODE_EXPR && node_a(ctx.1, expr) == EXPR_LIT {
        let kind = node_b(ctx.1, expr);
        if kind == LIT_INT || kind == LIT_HEX {
            return node_c(ctx.1, expr);
        }
    }
    IDX_DYN
}

fn index_keys_conflict(ctx: &Ctx, a: i64, b: i64) -> bool {
    if a == NONE || b == NONE {
        return true;
    }
    if a == IDX_DYN || b == IDX_DYN {
        return true;
    }
    let na = list_len(ctx.2, a);
    let nb = list_len(ctx.2, b);
    let (short, nshort, long) = if na <= nb { (a, na, b) } else { (b, nb, a) };
    let mut idx = 0i64;
    while idx < nshort {
        if list_get(ctx.2, short, idx) != list_get(ctx.2, long, idx) {
            return false;
        }
        idx += 1;
    }
    true
}

fn index_suffix(ctx: &Ctx, key: i64) -> String {
    if key == NONE {
        return String::new();
    }
    if key == IDX_DYN {
        return String::from("[?]");
    }
    let mut out = String::new();
    let count = list_len(ctx.2, key);
    let mut idx = 0i64;
    while idx < count {
        let value = list_get(ctx.2, key, idx);
        if value == IDX_DYN {
            out.push_str("[?]");
        } else {
            out.push('[');
            out.push_str(&value.to_string());
            out.push(']');
        }
        idx += 1;
    }
    out
}

fn extend_loan_index(f: &mut F, ctx: &mut Ctx, loan: i64, level_key: i64) -> i64 {
    let cur = loan_at(f, loan).3;
    let new_key = if level_key == IDX_DYN {
        IDX_DYN
    } else if cur == NONE {
        let list = alloc_list(ctx.2);
        list_push(ctx.2, list, level_key);
        list
    } else if cur == IDX_DYN {
        IDX_DYN
    } else {
        let list = alloc_list(ctx.2);
        let count = list_len(ctx.2, cur);
        let mut idx = 0i64;
        while idx < count {
            let value = list_get(ctx.2, cur, idx);
            list_push(ctx.2, list, value);
            idx += 1;
        }
        list_push(ctx.2, list, level_key);
        list
    };
    if let Some(row) = f.3.get_mut(loan as usize) {
        row.3 = new_key;
    }
    new_key
}

fn stamp_op_index(f: &mut F, op: i64, key: i64) {
    if op < 0 {
        return;
    }
    if let Some(row) = f.4.get_mut(op as usize) {
        row.5 = key;
    }
}

fn walk_field_segments(f: &mut F, ctx: &mut Ctx, segs: i64, from: i64, mut cur_key: i64, mut cur_path: i64) -> (i64, i64) {
    let count = list_len(ctx.2, segs);
    let mut idx = from;
    while idx < count {
        let field = list_get(ctx.2, segs, idx);
        let base_kind = ty_kind_of(ctx.1, cur_key);
        if base_kind == TYD_STRUCT {
            let fkey = field_key_of(ctx, cur_key, field);
            if is_linear_key(ctx, fkey) == 1 && cur_path != NONE {
                cur_path = child_path(f, cur_path, field);
            }
            cur_key = fkey;
        }
        idx += 1;
    }
    (cur_key, cur_path)
}

fn dotted_seg_name(ctx: &mut Ctx, base: i64, segs: i64, count: i64) -> String {
    let mut text = name_text(ctx.0, base);
    let mut si = 1i64;
    while si < count {
        text = format!("{}.{}", text, name_text(ctx.0, list_get(ctx.2, segs, si)));
        si += 1;
    }
    text
}

fn walk_field_chain(f: &mut F, b: &mut B, ctx: &mut Ctx, expr: i64, binding: i64, mode: i64, prod: &mut Vec<i64>) {
    let row = binding_at(f, binding);
    let segs = node_b(ctx.1, expr);
    let count = list_len(ctx.2, segs);
    let span = expr_span(ctx.1, expr);
    let bkind = ty_kind_of(ctx.1, row.1);
    let through_mut = bkind == TYD_REF_MUT;
    let through_shared = bkind == TYD_REF;
    let mut cur_key = row.1;
    let cur_path = row.6;
    let start = 1i64;
    while ty_kind_of(ctx.1, cur_key) == TYD_REF || ty_kind_of(ctx.1, cur_key) == TYD_REF_MUT {
        cur_key = ty_elem_of(ctx.1, cur_key);
    }
    let (final_key, final_path) = walk_field_segments(f, ctx, segs, start, cur_key, cur_path);
    let final_is_lin = is_linear_key(ctx, final_key);
    if mode == MODE_BORROW || mode == MODE_MUT {
        let op_kind = if mode == MODE_MUT { OP_BORROW_M } else { OP_BORROW };
        let loan_kind = if mode == MODE_MUT { L_MUT } else { L_SHARED };
        check_pending_conflict(f, b, ctx, binding, mode, span);
        // `final_path` (computed above) must be threaded through, not
        // dropped as NONE: borrow_after_move_check reads an op's path to
        // decide whether it observes a moved value, and a field-chain
        // borrow with path NONE was therefore invisible to it — a borrow
        // of an already-moved field (`&s.b` after `s.b` was moved, or
        // `&s.n` after the whole of `s` was moved) compiled cleanly. This
        // mirrors what the MODE_VALUE arm below already does with
        // `final_path` for a field-chain *move*.
        let op = emit_op(f, op_kind, binding, final_path, (0, 0, NONE), span);
        b.6 = op;
        let loan = alloc_loan(f, binding, loan_kind, 0, NONE);
        b.3.push(loan);
        prod.clear();
        prod.push(loan);
        return;
    }
    if final_is_lin == 1 {
        if through_mut {
            let owner = referent_binding_of(f, binding);
            let rroot = if owner != NONE {
                root_path_of(f, owner)
            } else {
                root_path_of(f, binding)
            };
            if rroot < 0 {
                let text = dotted_seg_name(ctx, row.0, segs, count);
                push_error(ctx.3, &format!("cannot consume linear value '{}' through a mutable reference to an untracked temporary; bind the referent to a local first", text), span.0, span.1, span.2);
                return;
            }
            let elem_key = ty_elem_of(ctx.1, row.1);
            let (rkey, rpath) = walk_field_segments(f, ctx, segs, 1, elem_key, rroot);
            // `rkey` is NONE exactly when `rpath` never resolved (every linear
            // field walk that extends `rpath` also yields a concrete key), so
            // guarding on it adds no new failure mode for valid programs.
            if rkey == NONE || rpath == NONE || rpath == rroot {
                let text = dotted_seg_name(ctx, row.0, segs, count);
                push_error(ctx.3, &format!("cannot consume the whole value '{}' through a mutable reference; move the referent into a local and consume that instead", text), span.0, span.1, span.2);
                return;
            }
            let target = if owner != NONE { owner } else { binding };
            check_pending_conflict(f, b, ctx, target, MODE_VALUE, span);
            emit_op(f, OP_MOVE, target, rpath, (0, 0, 0), span);
            return;
        } else if through_shared {
            let text = dotted_seg_name(ctx, row.0, segs, count);
            push_error(ctx.3, &format!("cannot copy linear value '{}' out of a shared reference", text), span.0, span.1, span.2);
            return;
        }
    }
    if final_is_lin == 1 && final_path != NONE {
        check_pending_conflict(f, b, ctx, binding, MODE_VALUE, span);
        emit_op(f, OP_MOVE, binding, final_path, (0, 0, 0), span);
        return;
    }
    emit_op(f, OP_READ, binding, NONE, (0, 0, 0), span);
}

// The typechecker attached one fact row per (canonical struct key, field
// name) carrying the substituted field key; no ITEM_STRUCT re-walk and no
// re-run of generic substitution here (Single-Fact Rule).
fn field_key_of(ctx: &mut Ctx, key: i64, field: i64) -> i64 {
    let row = find_fieldkey(ctx.1, key, field);
    if row == NONE {
        NONE
    } else {
        fieldkey_key_of(ctx.1, row)
    }
}

fn assign_target_of(f: &mut F, b: &mut B, ctx: &mut Ctx, target: i64) -> (i64, i64, i64, i64) {
    if node_tag(ctx.1, target) != NODE_EXPR {
        return (NONE, NONE, 0, NONE);
    }
    let kind = node_a(ctx.1, target);
    if kind == EXPR_PATH {
        let segs = node_b(ctx.1, target);
        let count = list_len(ctx.2, segs);
        let first = list_first(ctx.2, segs);
        let binding = lookup_name(b, first);
        if count == 1 {
            return (binding, NONE, 0, NONE);
        }
        if binding == NONE {
            return (NONE, NONE, 1, NONE);
        }
        return field_assign_target(f, ctx, binding, segs);
    }
    if kind == EXPR_FIELD_ACCESS {
        let base = node_b(ctx.1, target);
        let field = node_c(ctx.1, target);
        if node_tag(ctx.1, base) == NODE_EXPR && node_a(ctx.1, base) == EXPR_PATH {
            let segs = node_b(ctx.1, base);
            let count = list_len(ctx.2, segs);
            let first = list_first(ctx.2, segs);
            let binding = lookup_name(b, first);
            if binding == NONE {
                expr_effects(f, b, ctx, base, MODE_MUT, NONE, &mut Vec::new());
                return (NONE, NONE, 1, NONE);
            }
            if count == 1 {
                let row = binding_at(f, binding);
                let bkind = ty_kind_of(ctx.1, row.1);
            if bkind == TYD_REF || bkind == TYD_REF_MUT {
                let owner = referent_binding_of(f, binding);
                let self_owned = bkind == TYD_REF_MUT && root_path_of(f, binding) >= 0;
                let cur_key = ty_elem_of(ctx.1, row.1);
                let mut cur_path = if owner != NONE {
                    root_path_of(f, owner)
                } else if self_owned {
                    root_path_of(f, binding)
                } else {
                    NONE
                };
                let fkey = field_key_of(ctx, cur_key, field);
                if is_linear_key(ctx, fkey) == 1 && cur_path != NONE {
                    cur_path = child_path(f, cur_path, field);
                }
                return (binding, cur_path, 1, if owner != NONE { owner } else if self_owned { binding } else { NONE });
            }
                let cur_key = row.1;
                let mut cur_path = row.6;
                let fkey = field_key_of(ctx, cur_key, field);
                if is_linear_key(ctx, fkey) == 1 && cur_path != NONE {
                    cur_path = child_path(f, cur_path, field);
                }
                return (binding, cur_path, 2, NONE);
            }
            return field_assign_target(f, ctx, binding, segs);
        }
        expr_effects(f, b, ctx, base, MODE_MUT, NONE, &mut Vec::new());
        return (NONE, NONE, 1, NONE);
    }
    (NONE, NONE, 0, NONE)
}

fn field_assign_target(f: &mut F, ctx: &mut Ctx, binding: i64, segs: i64) -> (i64, i64, i64, i64) {
    let row = binding_at(f, binding);
    let bkind = ty_kind_of(ctx.1, row.1);
    if bkind == TYD_REF || bkind == TYD_REF_MUT {
        let owner = referent_binding_of(f, binding);
        let self_owned = bkind == TYD_REF_MUT && root_path_of(f, binding) >= 0;
        let mut cur_key = ty_elem_of(ctx.1, row.1);
        let mut cur_path = if owner != NONE {
            root_path_of(f, owner)
        } else if self_owned {
            root_path_of(f, binding)
        } else {
            NONE
        };
        let count = list_len(ctx.2, segs);
        let mut idx = 1i64;
        while idx < count {
            let field = list_get(ctx.2, segs, idx);
            let fkey = field_key_of(ctx, cur_key, field);
            if is_linear_key(ctx, fkey) == 1 && cur_path != NONE {
                cur_path = child_path(f, cur_path, field);
            }
            cur_key = fkey;
            idx += 1;
        }
        return (binding, cur_path, 1, if owner != NONE { owner } else if self_owned { binding } else { NONE });
    }
    let mut cur_key = row.1;
    let mut cur_path = row.6;
    let count = list_len(ctx.2, segs);
    let mut idx = 1i64;
    while idx < count {
        let field = list_get(ctx.2, segs, idx);
        let fkey = field_key_of(ctx, cur_key, field);
        if is_linear_key(ctx, fkey) == 1 && cur_path != NONE {
            cur_path = child_path(f, cur_path, field);
        }
        cur_key = fkey;
        idx += 1;
    }
    (binding, cur_path, 2, NONE)
}

fn referent_binding_of(f: &F, binding: i64) -> i64 {
    let mut owner = NONE;
    let mut ok = true;
    let mut visited: Vec<i64> = Vec::new();
    origin_owners_of(f, binding, &mut owner, &mut ok, &mut visited);
    if ok {
        owner
    } else {
        NONE
    }
}

fn origin_owners_of(f: &F, binding: i64, owner: &mut i64, ok: &mut bool, visited: &mut Vec<i64>) {
    if !*ok || list_has(visited, binding) {
        return;
    }
    visited.push(binding);
    // Backward scan: the most recent bind/assign of this binding determines
    // its current referents.  A forward scan returns on the first
    // (stale) re-initialisation and can resolve a reassigned &mut binding
    // to its old referent.  Only loan-bearing ops carry referent facts;
    // a plain value binding has no loans to contribute.
    let mut op = f.4.len() as i64 - 1;
    while op >= 0 {
        let row = op_at(f, op);
        // Loans are read for reference bindings and for any binding whose
        // OP_BIND/OP_ASSIGN carries loans: a struct literal whose field
        // initialisers borrow keeps those field loans on its own bind, so a
        // later borrow of `s.f` resolves back to the underlying owner.
        if row.1 == binding
            && (row.0 == OP_BIND || row.0 == OP_ASSIGN)
            && (row.3 == 1 || !op_loans_at(f, op).is_empty())
        {
            let loans = op_loans_at(f, op);
            let mut idx = 0usize;
            while idx < loans.len() {
                let entry = match loans.get(idx) {
                    Some(value) => *value,
                    None => break,
                };
                if is_ref_origin(entry) {
                    origin_owners_of(f, -1 - entry, owner, ok, visited);
                } else {
                    let lrow = loan_at(f, entry);
                    let o = lrow.0;
                    if o < 0 {
                        idx += 1;
                        continue;
                    }
                    let orow = binding_at(f, o);
                    if orow.3 == 1 {
                        if orow.4 == 1 {
                            *ok = false;
                        } else {
                            origin_owners_of(f, o, owner, ok, visited);
                        }
                    } else if *owner == NONE {
                        *owner = o;
                    } else if *owner != o {
                        *ok = false;
                    }
                }
                idx += 1;
            }
            return;
        }
        op -= 1;
    }
}

fn dotted_name_of(f: &F, ctx: &mut Ctx, binding: i64, path: i64) -> String {
    let base = name_text(ctx.0, binding_at(f, binding).0);
    if path == NONE || is_root_path(f, path) {
        return base;
    }
    let mut names: Vec<i64> = Vec::new();
    let mut p = path;
    while p != NONE && !is_root_path(f, p) {
        names.push(path_at(f, p).1);
        p = path_at(f, p).0;
    }
    let mut text = base;
    let mut idx = names.len();
    while idx > 0 {
        idx -= 1;
        match names.get(idx) {
            Some(name) => text = format!("{}.{}", text, name_text(ctx.0, *name)),
            None => break,
        }
    }
    text
}

fn all_children_live(f: &F, state: &[i64], parent: i64) -> bool {
    let mut idx = 0usize;
    while idx < f.2.len() {
        if path_at(f, idx as i64).0 == parent {
            let cst = state_at(state, idx as i64);
            if cst == ST_MOVED || cst == ST_PARTIAL {
                return false;
            }
        }
        idx += 1;
    }
    true
}

fn unary_effects(f: &mut F, b: &mut B, ctx: &mut Ctx, expr: i64, ret: i64, prod: &mut Vec<i64>) -> i64 {
    let op = node_b(ctx.1, expr);
    let operand = node_c(ctx.1, expr);
    if op == UN_REF {
        return expr_effects(f, b, ctx, operand, MODE_BORROW, ret, prod);
    }
    if op == UN_REF_MUT {
        return expr_effects(f, b, ctx, operand, MODE_MUT, ret, prod);
    }
    expr_effects(f, b, ctx, operand, MODE_VALUE, ret, prod)
}

fn binary_effects(f: &mut F, b: &mut B, ctx: &mut Ctx, expr: i64, ret: i64, prod: &mut Vec<i64>) -> i64 {
    let lhs = node_c(ctx.1, expr);
    let rhs = node_d(ctx.1, expr);
    expr_effects(f, b, ctx, lhs, MODE_VALUE, ret, prod);
    expr_effects(f, b, ctx, rhs, MODE_VALUE, ret, prod)
}

// The typechecker attached the trait method's fn node to the dispatch row
// when it created it; no ITEM_TRAIT method-list re-search (Single-Fact
// Rule).
fn trait_method_of(ctx: &mut Ctx, expr: i64) -> i64 {
    let trow = find_trait_call(ctx.1, expr);
    if trow == NONE {
        NONE
    } else {
        trait_call_method_node(ctx.1, trow)
    }
}

// The typechecker attached the canonical key to every parameter type node
// (trait method signatures included), so the mode reads the key's kind
// instead of re-deriving it from raw NODE_TY tags (Single-Fact Rule).
fn param_mode_of(nodes: &[i64], ty_node: i64) -> i64 {
    let kind = ty_kind_of(nodes, ty_key_of(nodes, ty_node));
    if kind == TYD_REF {
        MODE_BORROW
    } else if kind == TYD_REF_MUT {
        MODE_MUT
    } else {
        MODE_VALUE
    }
}

fn ret_is_ref_node(nodes: &[i64], ty_node: i64) -> i64 {
    let kind = ty_kind_of(nodes, ty_key_of(nodes, ty_node));
    if kind == TYD_REF || kind == TYD_REF_MUT || kind == TYD_SLICE {
        1
    } else {
        0
    }
}

fn call_origin_of(ctx: &mut Ctx, summary_key: Option<i64>, arg_prods: &[Vec<i64>], prod: &mut Vec<i64>) {
    let positions = match summary_key {
        Some(fn_node) => summary_of(ctx.4, fn_node),
        None => None,
    };
    match positions {
        Some(positions) => {
            let mut idx = 0usize;
            while idx < positions.len() {
                match positions.get(idx) {
                    Some(position) => {
                        if let Some(arg_prod) = arg_prods.get(*position as usize) {
                            append_prod_unique(prod, arg_prod);
                        }
                    }
                    None => break,
                }
                idx += 1;
            }
        }
        None => {
            let mut idx = 0usize;
            while idx < arg_prods.len() {
                match arg_prods.get(idx) {
                    Some(arg_prod) => append_prod_unique(prod, arg_prod),
                    None => break,
                }
                idx += 1;
            }
        }
    }
}

fn call_effects(f: &mut F, b: &mut B, ctx: &mut Ctx, expr: i64, ret: i64, prod: &mut Vec<i64>) -> i64 {
    let inst = expr_sym_of(ctx.1, expr);
    let args = node_d(ctx.1, expr);
    let argc = list_len(ctx.2, args);
    let op = native_op_of(ctx, expr);
    if node_tag(ctx.1, inst) != NODE_INST {
        let method = trait_method_of(ctx, expr);
        if method == NONE {
            push_internal(ctx.3, "internal error: call without an instance or trait-dispatch row in borrow checking");
            let mut idx = 0i64;
            while idx < argc {
                expr_effects(f, b, ctx, list_get(ctx.2, args, idx), MODE_VALUE, ret, prod);
                idx += 1;
            }
            prod.clear();
            return cur(b);
        }
        let params = node_c(ctx.1, method);
        let mut arg_prods: Vec<Vec<i64>> = Vec::new();
        let mut idx = 0i64;
        while idx < argc {
            let arg = list_get(ctx.2, args, idx);
            let pty = node_b(ctx.1, list_get(ctx.2, params, idx));
            let mode = param_mode_of(ctx.1, pty);
            let mut arg_prod: Vec<i64> = Vec::new();
            expr_effects(f, b, ctx, arg, mode, ret, &mut arg_prod);
            if mode == MODE_MUT && op != NAT_VEC_POP && op != NAT_HASH_MAP_REMOVE {
                fill_container_if_mut_arg(f, b, ctx, arg);
            }
            arg_prods.push(arg_prod);
            idx += 1;
        }
        if ret_is_ref_node(ctx.1, node_d(ctx.1, method)) == 0 {
            prod.clear();
        } else {
            call_origin_of(ctx, None, &arg_prods, prod);
        }
        return cur(b);
    }
    let params = inst_params_of(ctx.1, inst);
    let mut arg_prods: Vec<Vec<i64>> = Vec::new();
    let mut idx = 0i64;
    while idx < argc {
        let arg = list_get(ctx.2, args, idx);
        let pkey = list_get(ctx.2, params, idx);
        let pkind = ty_kind_of(ctx.1, pkey);
        let mode = if pkind == TYD_REF {
            MODE_BORROW
        } else if pkind == TYD_REF_MUT {
            MODE_MUT
        } else {
            MODE_VALUE
        };
        let mut arg_prod: Vec<i64> = Vec::new();
        expr_effects(f, b, ctx, arg, mode, ret, &mut arg_prod);
        if mode == MODE_MUT && op != NAT_VEC_POP && op != NAT_HASH_MAP_REMOVE {
            fill_container_if_mut_arg(f, b, ctx, arg);
        }
        arg_prods.push(arg_prod);
        idx += 1;
    }
    let ret_key = inst_ret_of(ctx.1, inst);
    if is_ref_key(ctx.1, ret_key) {
        if op == NAT_SLICE_VIEW {
            prod.clear();
            if let Some(first_prod) = arg_prods.first() {
                append_prod_unique(prod, first_prod);
            }
        } else {
            call_origin_of(ctx, Some(inst_fn_of(ctx.1, inst)), &arg_prods, prod);
        }
    } else {
        prod.clear();
    }
    if op == NAT_VEC_FREE || op == NAT_HASH_MAP_FREE {
        let free_arg = list_first(ctx.2, args);
        let container = container_binding_of(b, ctx, free_arg);
        if container >= 0 {
            emit_op(f, OP_CONT_FREE, container, NONE, (0, 0, 0), expr_span(ctx.1, expr));
        } else if container_has_linear_elem(ctx, expr_ty_of(ctx.1, free_arg)) && create_provenance(ctx, b, free_arg) != 1 {
            // The freed value isn't a named binding (e.g. `vec_free(make_full_vec())`,
            // freeing a call result directly) — the drain check above is keyed by
            // binding and has nothing to key off of here. `create_provenance` still
            // clears an anonymous value that's directly and provably fresh (a native
            // create call, or a match on one) the same way it does for a `let`
            // binding; anything else unresolvable starts MayContain, symmetric with
            // a by-value container *parameter* (see the OP_CONT_MAY emitted for one
            // above) — there's no binding to attach a deferred OP_CONT_FREE to and
            // no later point where one could become resolvable, so the answer has
            // to be immediate.
            push_error(
                ctx.3,
                "cannot free container holding linear elements: drain the container (pop all elements) before freeing",
                node_file(ctx.1, expr),
                node_start(ctx.1, expr),
                node_end(ctx.1, expr),
            );
        }
    }
    cur(b)
}

fn struct_effects(f: &mut F, b: &mut B, ctx: &mut Ctx, expr: i64, ret: i64, prod: &mut Vec<i64>) -> i64 {
    let values = node_d(ctx.1, expr);
    let count = list_len(ctx.2, values);
    let mut idx = 0i64;
    while idx < count {
        expr_effects(f, b, ctx, list_get(ctx.2, values, idx), MODE_VALUE, ret, prod);
        idx += 1;
    }
    cur(b)
}

fn array_effects(f: &mut F, b: &mut B, ctx: &mut Ctx, expr: i64, ret: i64, prod: &mut Vec<i64>) -> i64 {
    let elems = node_b(ctx.1, expr);
    let count = list_len(ctx.2, elems);
    let mut idx = 0i64;
    while idx < count {
        expr_effects(f, b, ctx, list_get(ctx.2, elems, idx), MODE_VALUE, ret, prod);
        idx += 1;
    }
    cur(b)
}

fn path_root_binding_of(ctx: &mut Ctx, b: &B, expr: i64) -> i64 {
    if node_tag(ctx.1, expr) != NODE_EXPR || node_a(ctx.1, expr) != EXPR_PATH {
        return NONE;
    }
    let segs = node_b(ctx.1, expr);
    let first = list_first(ctx.2, segs);
    lookup_name(b, first)
}

fn wrap_stmt_list(lists: &mut Vec<Vec<i64>>, stmt: i64) -> i64 {
    let list = alloc_list(lists);
    list_push(lists, list, stmt);
    list
}

fn match_effects(f: &mut F, b: &mut B, ctx: &mut Ctx, expr: i64, ret: i64, prod: &mut Vec<i64>) -> i64 {
    let scrutinee = node_b(ctx.1, expr);
    let arms = node_c(ctx.1, expr);
    let span = expr_span(ctx.1, expr);
    let mut scrut_prod: Vec<i64> = Vec::new();
    let cont = expr_effects(f, b, ctx, scrutinee, MODE_VALUE, ret, &mut scrut_prod);
    let scrut_root = path_root_binding_of(ctx, b, scrutinee);
    let scrut_key = expr_ty_of(ctx.1, scrutinee);
    let known_empty = create_provenance(ctx, b, scrutinee);
    let extr_container = if node_a(ctx.1, scrutinee) == EXPR_CALL && node_c(ctx.1, scrutinee) != NONE {
        lookup_name(b, node_c(ctx.1, scrutinee))
    } else if scrut_root != NONE {
        extraction_container_of_binding(&b.8, scrut_root)
    } else {
        NONE
    };
    let join = new_block(f, b, BLK_JOIN, NONE, span);
    let count = list_len(ctx.2, arms);
    let mut idx = 0i64;
    while idx < count {
        let arm = list_get(ctx.2, arms, idx);
        let pat = node_a(ctx.1, arm);
        let body_stmt = node_b(ctx.1, arm);
        let arm_entry = new_block(f, b, BLK_STMT, arm, span);
        let scrut = (&scrut_prod[..], scrut_root);
        pattern_effects(f, b, ctx, pat, scrut, known_empty);
        // The empty/error arm of an extraction match proves the container
        // drained: vec_pop errors only on an empty vector, and the surface
        // contract treats the remove KeyNotFound arm the same way.
        if extr_container != NONE && arm_is_result_err(ctx, scrut_key, pat, arms, idx) {
            emit_op(f, OP_CONT_EMPTY, extr_container, NONE, (0, 0, 0), span);
        }
        let body = wrap_stmt_list(ctx.2, body_stmt);
        let body_entry = build_list(f, b, ctx, body, join, ret, prod);
        add_edge(f, arm_entry, body_entry);
        add_edge(f, cont, arm_entry);
        idx += 1;
    }
    resume(f, b, join);
    join
}

fn pattern_effects(f: &mut F, b: &mut B, ctx: &mut Ctx, pat: i64, scrut: (&[i64], i64), known_empty: i64) {
    if node_tag(ctx.1, pat) != NODE_PAT {
        return;
    }
    let kind = node_a(ctx.1, pat);
    let span = (node_file(ctx.1, pat), node_start(ctx.1, pat), node_end(ctx.1, pat));
    if kind == PAT_BIND {
        let name = node_b(ctx.1, pat);
        let key = pat_ty_of(ctx.1, pat);
        bind_pattern_name(f, b, ctx, (name, key), span, scrut, known_empty);
        return;
    }
    if kind == PAT_VARIANT {
        let payloads = node_c(ctx.1, pat);
        let count = list_len(ctx.2, payloads);
        let mut idx = 0i64;
        while idx < count {
            pattern_effects(f, b, ctx, list_get(ctx.2, payloads, idx), scrut, known_empty);
            idx += 1;
        }
        return;
    }
    if kind == PAT_ARRAY {
        let elems = node_b(ctx.1, pat);
        let count = list_len(ctx.2, elems);
        let mut idx = 0i64;
        while idx < count {
            pattern_effects(f, b, ctx, list_get(ctx.2, elems, idx), scrut, known_empty);
            idx += 1;
        }
        let rest = node_c(ctx.1, pat);
        if rest != NONE {
            let rest_key = pat_rest_key_of(ctx.1, pat);
            bind_pattern_name(f, b, ctx, (rest, rest_key), span, scrut, known_empty);
        }
    }
}

fn bind_pattern_name(f: &mut F, b: &mut B, ctx: &mut Ctx, binding: (i64, i64), span: (i64, i64, i64), scrut: (&[i64], i64), known_empty: i64) {
    let (name, key) = binding;
    let flags = (is_linear_key(ctx, key), if is_ref_key(ctx.1, key) { 1 } else { 0 }, 0, 0);
    let binding = bind_var(f, b, ctx, name, key, flags, span);
    let op = emit_op(f, OP_BIND, binding, NONE, (flags.1, 1, 0), span);
    if flags.1 == 1 {
        let mut loans: Vec<i64> = Vec::new();
        let mut idx = 0usize;
        while idx < scrut.0.len() {
            match scrut.0.get(idx) {
                Some(entry) => loans.push(*entry),
                None => break,
            }
            idx += 1;
        }
        if loans.is_empty() && scrut.1 != NONE {
            let loan = alloc_loan(f, scrut.1, L_SHARED, 0, NONE);
            loans.push(loan);
        }
        set_op_loans(f, op, &loans);
    }
    // A container bound from a match is empty only when the scrutinee is a
    // native create call; every other provenance may carry linear elements.
    if container_has_linear_elem(ctx, key) {
        if known_empty == 1 {
            emit_op(f, OP_CONT_EMPTY, binding, NONE, (0, 0, 0), span);
        } else {
            emit_op(f, OP_CONT_MAY, binding, NONE, (0, 0, 0), span);
        }
    }
}

fn try_effects(f: &mut F, b: &mut B, ctx: &mut Ctx, expr: i64, ret: i64, prod: &mut Vec<i64>) -> i64 {
    let inner = node_b(ctx.1, expr);
    let span = expr_span(ctx.1, expr);
    let cont = expr_effects(f, b, ctx, inner, MODE_VALUE, ret, prod);
    emit_op(f, OP_EXIT, NONE, NONE, (0, EX_TRY, 0), span);
    cont
}

fn collect_fn_nodes(nodes: &[i64], lists: &[Vec<i64>], list: i64, out: &mut Vec<i64>) {
    let count = list_len(lists, list);
    let mut idx = 0i64;
    while idx < count {
        let item = list_get(lists, list, idx);
        if node_tag(nodes, item) == NODE_ITEM {
            let kind = node_a(nodes, item);
            if kind == ITEM_MODULE {
                collect_fn_nodes(nodes, lists, node_e(nodes, item), out);
            } else if kind == ITEM_FUN || kind == ITEM_NATIVE_FUN {
                out.push(node_d(nodes, item));
            } else if kind == ITEM_IMPL {
                collect_fn_list_nodes(nodes, lists, node_f(nodes, item), out);
            } else if kind == ITEM_TRAIT {
                collect_fn_list_nodes(nodes, lists, node_e(nodes, item), out);
            }
        }
        idx += 1;
    }
}

fn collect_fn_list_nodes(nodes: &[i64], lists: &[Vec<i64>], list: i64, out: &mut Vec<i64>) {
    let count = list_len(lists, list);
    let mut idx = 0i64;
    while idx < count {
        let item = list_get(lists, list, idx);
        if node_tag(nodes, item) == NODE_FN {
            out.push(item);
        }
        idx += 1;
    }
}

fn max_fn_params(nodes: &[i64], lists: &[Vec<i64>], fns: &[i64]) -> i64 {
    let mut max = 0i64;
    let mut idx = 0usize;
    while idx < fns.len() {
        match fns.get(idx) {
            Some(fn_node) => {
                let count = list_len(lists, node_c(nodes, *fn_node));
                if count > max {
                    max = count;
                }
            }
            None => break,
        }
        idx += 1;
    }
    max
}

pub fn borrow_check(
    names: &mut Vec<String>,
    nodes: &mut Vec<i64>,
    lists: &mut Vec<Vec<i64>>,
    errors: &mut Vec<Diag>,
    notes: &mut Vec<Note>,
    root: i64,
    ext_mods: &[(i64, i64)],
) -> bool {
    let before = errors.len();

    let mut summaries: Vec<(i64, Vec<i64>)> = Vec::new();
    let mut scratch: Vec<Diag> = Vec::new();
    let mut scratch_notes: Vec<Note> = Vec::new();
    let mut fns: Vec<i64> = Vec::new();
    collect_fn_nodes(nodes, lists, root, &mut fns);
    let mut m = 0usize;
    while m < ext_mods.len() {
        match ext_mods.get(m) {
            Some(pair) => collect_fn_nodes(nodes, lists, pair.1, &mut fns),
            None => break,
        }
        m += 1;
    }
    let cap = fns.len() as i64 * (max_fn_params(nodes, lists, &fns) + 1) + fns.len() as i64 + 1;
    let mut round = 0i64;
    loop {
        let mut changed = false;
        let mut fi = 0usize;
        while fi < fns.len() {
            match fns.get(fi) {
                Some(fn_node) => {
                    let sources = {
                        let mut f: F = (
                            Vec::new(),
                            Vec::new(),
                            Vec::new(),
                            Vec::new(),
                            Vec::new(),
                            Vec::new(),
                            Vec::new(),
                            Vec::new(),
                            Vec::new(),
                            Vec::new(),
                            Vec::new(),
                        );
                        let mut b: B = (Vec::new(), Vec::new(), Vec::new(), Vec::new(), NONE, NONE, NONE, NONE, Vec::new(), Vec::new());
                        let err_id = find_name(names, "Err");
                        let ok_id = find_name(names, "Ok");
                        let mut ctx: Ctx = (names, nodes, lists, &mut scratch, &mut summaries, err_id, ok_id, &mut scratch_notes);
                        if build_fn(&mut f, &mut b, &mut ctx, *fn_node) {
                            compute_summary(&f, &mut ctx, 0, *fn_node)
                        } else {
                            None
                        }
                    };
                    scratch.clear();
                    scratch_notes.clear();
                    changed |= refine_summary(&mut summaries, *fn_node, sources);
                }
                None => break,
            }
            fi += 1;
        }
        round += 1;
        if !changed {
            break;
        }
        if round > cap {
            push_internal(errors, "internal: callee-origin summaries did not converge");
            return false;
        }
    }

    check_item_list(names, nodes, lists, errors, notes, &mut summaries, root);
    let mut idx = 0usize;
    while idx < ext_mods.len() {
        match ext_mods.get(idx) {
            Some(pair) => check_item_list(names, nodes, lists, errors, notes, &mut summaries, pair.1),
            None => break,
        }
        idx += 1;
    }
    errors.len() == before
}

fn check_item_list(
    names: &mut Vec<String>,
    nodes: &mut Vec<i64>,
    lists: &mut Vec<Vec<i64>>,
    errors: &mut Vec<Diag>,
    notes: &mut Vec<Note>,
    summaries: &mut Vec<(i64, Vec<i64>)>,
    list: i64,
) {
    let count = list_len(lists, list);
    let mut idx = 0i64;
    while idx < count {
        let item = list_get(lists, list, idx);
        if node_tag(nodes, item) == NODE_ITEM {
            let kind = node_a(nodes, item);
            if kind == ITEM_MODULE {
                check_item_list(names, nodes, lists, errors, notes, summaries, node_e(nodes, item));
            } else if kind == ITEM_FUN || kind == ITEM_NATIVE_FUN {
                check_fn(names, nodes, lists, errors, notes, summaries, node_d(nodes, item));
            } else if kind == ITEM_IMPL {
                check_fn_list(names, nodes, lists, errors, notes, summaries, node_f(nodes, item));
            } else if kind == ITEM_TRAIT {
                check_fn_list(names, nodes, lists, errors, notes, summaries, node_e(nodes, item));
            }
        }
        idx += 1;
    }
}

fn check_fn_list(
    names: &mut Vec<String>,
    nodes: &mut Vec<i64>,
    lists: &mut Vec<Vec<i64>>,
    errors: &mut Vec<Diag>,
    notes: &mut Vec<Note>,
    summaries: &mut Vec<(i64, Vec<i64>)>,
    list: i64,
) {
    let count = list_len(lists, list);
    let mut idx = 0i64;
    while idx < count {
        check_fn(names, nodes, lists, errors, notes, summaries, list_get(lists, list, idx));
        idx += 1;
    }
}

fn check_fn(
    names: &mut Vec<String>,
    nodes: &mut Vec<i64>,
    lists: &mut Vec<Vec<i64>>,
    errors: &mut Vec<Diag>,
    notes: &mut Vec<Note>,
    summaries: &mut Vec<(i64, Vec<i64>)>,
    fn_node: i64,
) {
    if node_tag(nodes, fn_node) != NODE_FN {
        return;
    }
    let mut f: F = (
        Vec::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
    );
    let mut b: B = (Vec::new(), Vec::new(), Vec::new(), Vec::new(), NONE, NONE, NONE, NONE, Vec::new(), Vec::new());
    let err_id = find_name(names, "Err");
    let ok_id = find_name(names, "Ok");
    let mut ctx: Ctx = (names, nodes, lists, errors, summaries, err_id, ok_id, notes);
    if !build_fn(&mut f, &mut b, &mut ctx, fn_node) {
        return;
    }
    let entry = 0i64;
    analyze_fn(&mut f, &mut ctx, entry);
}

fn analyze_fn(f: &mut F, ctx: &mut Ctx, entry: i64) {
    let live_after = compute_liveness(f, ctx);
    let flow = linear_fixpoint(f, ctx, entry);
    let entry_origins = origin_fixpoint(f, ctx, entry);
    let entry_cont = container_fixpoint(f, ctx, entry);
    report(f, ctx, &live_after, &flow, &entry_origins, &entry_cont);
}

fn same_set(a: &[i64], b: &[i64]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut idx = 0usize;
    while idx < a.len() {
        match a.get(idx) {
            Some(v) => {
                if !list_has(b, *v) {
                    return false;
                }
            }
            None => break,
        }
        idx += 1;
    }
    true
}

fn remove_value(set: &mut Vec<i64>, value: i64) {
    let mut idx = 0usize;
    while idx < set.len() {
        match set.get(idx) {
            Some(v) => {
                if *v == value {
                    set.remove(idx);
                    return;
                }
            }
            None => break,
        }
        idx += 1;
    }
}

fn append_unique(set: &mut Vec<i64>, value: i64) {
    if value >= 0 && !list_has(set, value) {
        set.push(value);
    }
}

fn append_list_unique(set: &mut Vec<i64>, other: &[i64]) {
    let mut idx = 0usize;
    while idx < other.len() {
        match other.get(idx) {
            Some(v) => append_unique(set, *v),
            None => break,
        }
        idx += 1;
    }
}

fn append_prod_unique(set: &mut Vec<i64>, other: &[i64]) {
    let mut idx = 0usize;
    while idx < other.len() {
        match other.get(idx) {
            Some(v) => {
                if !list_has(set, *v) {
                    set.push(*v);
                }
            }
            None => break,
        }
        idx += 1;
    }
}

fn block_op_range(f: &F, block: i64) -> (i64, i64) {
    let row = block_at(f, block);
    let first = row.2;
    let mut last = block_op_end(f, block) - 1;
    if last < first {
        last = first - 1;
    }
    (first, last)
}

fn op_uses(f: &F, op: i64) -> i64 {
    let row = op_at(f, op);
    if row.0 == OP_READ
        || row.0 == OP_MOVE
        || row.0 == OP_BORROW
        || row.0 == OP_BORROW_M
        || (row.0 == OP_ASSIGN && row.4 == 1)
    {
        row.1
    } else {
        NONE
    }
}

fn op_defs(f: &F, op: i64) -> i64 {
    let row = op_at(f, op);
    if row.0 == OP_BIND || (row.0 == OP_ASSIGN && row.4 != 1) {
        row.1
    } else {
        NONE
    }
}

fn block_reborrows(f: &F, block: i64) -> Vec<i64> {
    let mut out: Vec<i64> = Vec::new();
    let (first, last) = block_op_range(f, block);
    let mut op = first;
    while op <= last {
        let row = op_at(f, op);
        if (row.0 == OP_BORROW || row.0 == OP_BORROW_M) && row.1 >= 0 && binding_at(f, row.1).3 == 1 {
            append_unique(&mut out, row.1);
        }
        op += 1;
    }
    out
}

fn compute_liveness(f: &F, ctx: &mut Ctx) -> Vec<Vec<i64>> {
    let nblocks = f.6.len() as i64;
    let nbind = f.0.len() as i64;
    let mut live_in: Vec<Vec<i64>> = Vec::new();
    let mut live_out: Vec<Vec<i64>> = Vec::new();
    let mut blk = 0i64;
    while blk < nblocks {
        live_in.push(Vec::new());
        live_out.push(Vec::new());
        blk += 1;
    }
    // Live sets hold binding indices: 2 sets per block (in/out), each growing at most nbind times.
    let cap = nblocks * nbind * 2 + 1;
    let mut guard = 0usize;
    loop {
        guard += 1;
        if guard > cap as usize {
            push_internal(ctx.3, "internal: liveness analysis did not converge");
            break;
        }
        let mut changed = false;
        let mut blk = 0i64;
        while blk < nblocks {
            let mut out: Vec<i64> = Vec::new();
            let succs = succ_of(f, blk);
            let mut si = 0usize;
            while si < succs.len() {
                match succs.get(si) {
                    Some(s) => {
                        if let Some(list) = live_in.get(*s as usize) {
                            append_list_unique(&mut out, list);
                        }
                    }
                    None => break,
                }
                si += 1;
            }
            append_list_unique(&mut out, &block_reborrows(f, blk));
            let mut inn = out.clone();
            let (first, last) = block_op_range(f, blk);
            let mut op = first;
            while op <= last {
                let def = op_defs(f, op);
                if def >= 0 {
                    remove_value(&mut inn, def);
                }
                let useb = op_uses(f, op);
                if useb >= 0 {
                    append_unique(&mut inn, useb);
                }
                op += 1;
            }
            if !same_set(&live_out[blk as usize], &out) {
                live_out[blk as usize] = out;
                changed = true;
            }
            if !same_set(&live_in[blk as usize], &inn) {
                live_in[blk as usize] = inn;
                changed = true;
            }
            blk += 1;
        }
        if !changed {
            break;
        }
    }
    let mut live_after: Vec<Vec<i64>> = Vec::new();
    let mut opi = 0i64;
    while opi < f.4.len() as i64 {
        live_after.push(Vec::new());
        opi += 1;
    }
    let mut blk = 0i64;
    while blk < nblocks {
        let mut set = live_out[blk as usize].clone();
        let (first, last) = block_op_range(f, blk);
        let mut op = last;
        while op >= first {
            if let Some(slot) = live_after.get_mut(op as usize) {
                slot.clear();
                let mut j = 0usize;
                while j < set.len() {
                    match set.get(j) {
                        Some(v) => slot.push(*v),
                        None => break,
                    }
                    j += 1;
                }
            }
            let useb = op_uses(f, op);
            if useb >= 0 {
                append_unique(&mut set, useb);
            }
            let def = op_defs(f, op);
            if def >= 0 {
                remove_value(&mut set, def);
            }
            op -= 1;
        }
        blk += 1;
    }
    live_after
}

fn unbound_state(npaths: i64) -> Vec<i64> {
    let mut out: Vec<i64> = Vec::new();
    let mut idx = 0i64;
    while idx < npaths {
        out.push(ST_UNBOUND);
        idx += 1;
    }
    out
}

fn same_state(a: &[i64], b: &[i64]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut idx = 0usize;
    while idx < a.len() {
        match a.get(idx) {
            Some(va) => match b.get(idx) {
                Some(vb) => {
                    if va != vb {
                        return false;
                    }
                }
                None => return false,
            },
            None => break,
        }
        idx += 1;
    }
    true
}

fn inc_has(inc: &[(i64, i64)], block: i64, path: i64) -> bool {
    let mut idx = 0usize;
    while idx < inc.len() {
        match inc.get(idx) {
            Some(pair) => {
                if pair.0 == block && pair.1 == path {
                    return true;
                }
            }
            None => break,
        }
        idx += 1;
    }
    false
}

// Lattice order: UNBOUND < LIVE < MOVED < PARTIAL.  The join is the least
// upper bound: UNBOUND joins to the other side, LIVE joins MOVED to MOVED,
// and any PARTIAL operand dominates, so entry states only ever rise.
fn join_linear(inn: &mut [i64], pout: &[i64], block: i64, inc: &mut Vec<(i64, i64)>) {
    let mut idx = 0usize;
    while idx < inn.len() {
        let a = state_at(inn, idx as i64);
        let b = state_at(pout, idx as i64);
        let joined;
        if a == ST_UNBOUND {
            joined = b;
        } else if b == ST_UNBOUND || a == b {
            joined = a;
        } else if a == ST_PARTIAL || b == ST_PARTIAL {
            joined = ST_PARTIAL;
        } else {
            joined = ST_MOVED;
            if !inc_has(inc, block, idx as i64) {
                inc.push((block, idx as i64));
            }
        }
        state_set(inn, idx as i64, joined);
        idx += 1;
    }
}

fn path_descends(f: &F, path: i64, ancestor: i64) -> bool {
    let mut cur = path_at(f, path).0;
    while cur != NONE {
        if cur == ancestor {
            return true;
        }
        cur = path_at(f, cur).0;
    }
    false
}

fn mark_descendants(f: &F, state: &mut [i64], path: i64, value: i64) {
    let mut idx = 0usize;
    while idx < f.2.len() {
        if path_descends(f, idx as i64, path) {
            state_set(state, idx as i64, value);
        }
        idx += 1;
    }
}

fn apply_move(f: &F, state: &mut [i64], binding: i64, path: i64, report: bool, ctx: &mut Ctx, span: (i64, i64, i64)) {
    if path < 0 {
        return;
    }
    let st = state_at(state, path);
    if report {
        let name = dotted_name_of(f, ctx, binding, path);
        if st == ST_MOVED {
            push_error(ctx.3, &format!("use of moved value '{}'", name), span.0, span.1, span.2);
        } else if st == ST_PARTIAL {
            push_error(ctx.3, &format!("cannot move out of partially moved value '{}'", name), span.0, span.1, span.2);
        }
    }
    if st == ST_UNBOUND || st == ST_MOVED || st == ST_PARTIAL {
        return;
    }
    state_set(state, path, ST_MOVED);
    mark_descendants(f, state, path, ST_MOVED);
    if !is_root_path(f, path) {
        let mut p = path_at(f, path).0;
        while p != NONE {
            let pst = state_at(state, p);
            if pst == ST_LIVE {
                state_set(state, p, ST_PARTIAL);
            }
            if pst == ST_MOVED {
                break;
            }
            p = path_at(f, p).0;
        }
    }
}

// Re-initialization is block-local: the MOVED->LIVE reset happens only in the
// block's exit copy, never in a join, and the LIVE/PARTIAL error paths leave
// the state untouched, so the block transform is entry-monotone and inter-block
// join states never regress downwards.
fn apply_assign(f: &F, state: &mut [i64], binding: i64, path: i64, report: bool, ctx: &mut Ctx, span: (i64, i64, i64)) {
    let root = root_path_of(f, binding);
    if root < 0 {
        return;
    }
    let target = if path == NONE { root } else { path };
    let name = dotted_name_of(f, ctx, binding, path);
    let st = state_at(state, target);
    let eff = if st == ST_UNBOUND && !is_root_path(f, target) {
        state_at(state, root)
    } else {
        st
    };
    if report {
        if eff == ST_LIVE {
            push_error(ctx.3, &format!("linear value '{}' is reassigned without being consumed", name), span.0, span.1, span.2);
            let row = binding_at(f, binding);
            explain_unconsumed(f, ctx, binding, &name, row.1);
            let bind_span = bind_span_of(f, binding);
            if bind_span.0 != NO_FILE {
                push_note_for_last(
                    ctx.3,
                    ctx.7,
                    "consume the existing value before assigning its replacement",
                    bind_span.0,
                    bind_span.1,
                    bind_span.2,
                    NOTE_GUIDANCE,
                );
            }
        } else if eff == ST_PARTIAL {
            push_error(ctx.3, &format!("cannot reassign partially moved value '{}'", name), span.0, span.1, span.2);
            let row = binding_at(f, binding);
            explain_unconsumed(f, ctx, binding, &name, row.1);
        }
    }
    if eff == ST_LIVE || eff == ST_PARTIAL {
        return;
    }
    if !is_root_path(f, target) && state_at(state, root) == ST_MOVED {
        if report {
            push_error(ctx.3, &format!("use of moved value '{}'", name), span.0, span.1, span.2);
        }
        return;
    }
    state_set(state, target, ST_LIVE);
    mark_descendants(f, state, target, ST_LIVE);
    if !is_root_path(f, target) {
        let mut p = path_at(f, target).0;
        while p != NONE {
            if state_at(state, p) != ST_PARTIAL {
                break;
            }
            if all_children_live(f, state, p) {
                state_set(state, p, ST_LIVE);
                p = path_at(f, p).0;
            } else {
                break;
            }
        }
    }
}

// Reports a borrow of a value that has already been moved.
//
// `apply_move` catches *moving* a moved value, but a borrow of one was not
// checked at all: `deallocate(block)` followed by `read_u8(&block, 0)`
// compiled cleanly and produced a real use-after-free, and closing a
// `File.Handle` and then writing through a borrow of it did the same.
// MANIFESTO principle 7 says a linear value "cannot be used after move";
// moving it twice is only one of the ways to do that, and the borrow is
// the more dangerous one, because the move it follows has already released
// the resource.
//
// The state is left untouched. Observing a moved value neither consumes it
// again nor revives it, so the dataflow is unchanged and the diagnostic is
// reported once per use site rather than folded into the move that caused
// it.
//
// Only `ST_MOVED` is reported, never `ST_PARTIAL`: a partially moved
// struct still has live fields, and borrowing it to reach one of those is
// exactly what partial-move tracking exists to allow.
fn borrow_after_move_check(f: &F, state: &[i64], binding: i64, path: i64, ctx: &mut Ctx, span: (i64, i64, i64)) {
    if path < 0 {
        return;
    }
    if state_at(state, path) != ST_MOVED {
        return;
    }
    let name = dotted_name_of(f, ctx, binding, path);
    push_error(ctx.3, &format!("use of moved value '{}'", name), span.0, span.1, span.2);
}

fn apply_block_linear(f: &F, block: i64, state: &mut [i64], report: bool, ctx: &mut Ctx) {
    let (first, last) = block_op_range(f, block);
    let mut op = first;
    while op <= last {
        let row = op_at(f, op);
        let kind = row.0;
        let binding = row.1;
        if kind == OP_BIND {
            if binding >= 0 && root_path_of(f, binding) != NONE {
                bind_state_live(f, state, binding);
            }
        } else if kind == OP_MOVE {
            apply_move(f, state, binding, row.2, report, ctx, (row.6, row.7, row.8));
        } else if kind == OP_ASSIGN {
            let tkind = row.4;
            if tkind == 1 && row.5 >= 0 && root_path_of(f, row.5) != NONE {
                apply_assign(f, state, row.5, row.2, report, ctx, (row.6, row.7, row.8));
            } else if tkind != 1 && binding >= 0 && root_path_of(f, binding) != NONE {
                let path = if tkind == 2 { row.2 } else { NONE };
                apply_assign(f, state, binding, path, report, ctx, (row.6, row.7, row.8));
            }
        }
        op += 1;
    }
}

// (per-block entry states, per-block exit states, inconsistent joins).
type LinearFlow = (Vec<Vec<i64>>, Vec<Vec<i64>>, Vec<(i64, i64)>);

fn linear_fixpoint(f: &F, ctx: &mut Ctx, entry: i64) -> LinearFlow {
    let nblocks = f.6.len() as i64;
    let npaths = f.2.len() as i64;
    let mut entry_state: Vec<Vec<i64>> = Vec::new();
    let mut exit_state: Vec<Vec<i64>> = Vec::new();
    let mut blk = 0i64;
    while blk < nblocks {
        entry_state.push(unbound_state(npaths));
        exit_state.push(unbound_state(npaths));
        blk += 1;
    }
    let mut inconsistencies: Vec<(i64, i64)> = Vec::new();
    // 2 state vectors per block (entry/exit) over npaths cells on a 4-state chain; each cell changes at most 4 times.
    let cap = nblocks * npaths * 8 + 1;
    let mut guard = 0usize;
    loop {
        guard += 1;
        if guard > cap as usize {
            push_internal(ctx.3, "internal: linear-consumption analysis did not converge");
            break;
        }
        // Inconsistencies are recorded only on the converged sweep.  A
        // (MOVED, LIVE) join that is inconsistent mid-iteration can later
        // converge as both sides reach MOVED; recording those intermediate
        // joins would report false positives.  Each sweep restarts the
        // record so the final break leaves only the converged joins.
        inconsistencies.clear();
        let mut changed = false;
        let mut blk = 0i64;
        while blk < nblocks {
            let mut inn = unbound_state(npaths);
            if blk != entry {
                let preds = pred_of(f, blk);
                let mut pi = 0usize;
                while pi < preds.len() {
                    match preds.get(pi) {
                        Some(p) => {
                            if let Some(list) = exit_state.get(*p as usize) {
                                join_linear(&mut inn, list, blk, &mut inconsistencies);
                            }
                        }
                        None => break,
                    }
                    pi += 1;
                }
            }
            let mut out = inn.clone();
            apply_block_linear(f, blk, &mut out, false, ctx);
            if !same_state(&entry_state[blk as usize], &inn) {
                entry_state[blk as usize] = inn;
                changed = true;
            }
            if !same_state(&exit_state[blk as usize], &out) {
                exit_state[blk as usize] = out;
                changed = true;
            }
            blk += 1;
        }
        if !changed {
            break;
        }
    }
    (entry_state, exit_state, inconsistencies)
}

fn cont_get(cont: &[i64], binding: i64) -> i64 {
    match cont.get(binding as usize) {
        Some(value) => *value,
        None => C_EMPTY,
    }
}

fn cont_set(cont: &mut [i64], binding: i64, value: i64) {
    if binding < 0 {
        return;
    }
    if let Some(cell) = cont.get_mut(binding as usize) {
        *cell = value;
    }
}

fn empty_cont(nbind: i64) -> Vec<i64> {
    let mut out: Vec<i64> = Vec::new();
    let mut idx = 0i64;
    while idx < nbind {
        out.push(C_EMPTY);
        idx += 1;
    }
    out
}

fn same_cont(a: &[i64], b: &[i64]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut idx = 0usize;
    while idx < a.len() {
        match a.get(idx) {
            Some(va) => match b.get(idx) {
                Some(vb) => {
                    if va != vb {
                        return false;
                    }
                }
                None => return false,
            },
            None => break,
        }
        idx += 1;
    }
    true
}

fn join_cont(inn: &mut [i64], pout: &[i64]) {
    let mut idx = 0usize;
    while idx < inn.len() {
        let a = match inn.get(idx) {
            Some(value) => *value,
            None => break,
        };
        let b = match pout.get(idx) {
            Some(value) => *value,
            None => break,
        };
        if b > a
            && let Some(cell) = inn.get_mut(idx)
        {
            *cell = b;
        }
        idx += 1;
    }
}

fn apply_block_container(f: &F, block: i64, cont: &mut [i64]) {
    let (first, last) = block_op_range(f, block);
    let mut op = first;
    while op <= last {
        let row = op_at(f, op);
        let kind = row.0;
        if kind == OP_CONT_EMPTY {
            cont_set(cont, row.1, C_EMPTY);
        } else if kind == OP_CONT_MAY {
            cont_set(cont, row.1, C_MAY);
        }
        op += 1;
    }
}

// The per-container-binding drain lattice (EmptyOrDrained < MayContain) is
// joined with the least upper bound at block entries, so every cell changes
// at most once and the fixpoint converges monotonically over loops.
fn container_fixpoint(f: &F, ctx: &mut Ctx, entry: i64) -> Vec<Vec<i64>> {
    let nblocks = f.6.len() as i64;
    let nbind = f.0.len() as i64;
    let mut entry_cont: Vec<Vec<i64>> = Vec::new();
    let mut exit_cont: Vec<Vec<i64>> = Vec::new();
    let mut blk = 0i64;
    while blk < nblocks {
        entry_cont.push(empty_cont(nbind));
        exit_cont.push(empty_cont(nbind));
        blk += 1;
    }
    let cap = nblocks * nbind * 2 + 1;
    let mut guard = 0usize;
    loop {
        guard += 1;
        if guard > cap as usize {
            push_internal(ctx.3, "internal: container-drain analysis did not converge");
            break;
        }
        let mut changed = false;
        let mut blk = 0i64;
        while blk < nblocks {
            let mut inn = empty_cont(nbind);
            if blk != entry {
                let preds = pred_of(f, blk);
                let mut pi = 0usize;
                while pi < preds.len() {
                    match preds.get(pi) {
                        Some(p) => {
                            if let Some(list) = exit_cont.get(*p as usize) {
                                join_cont(&mut inn, list);
                            }
                        }
                        None => break,
                    }
                    pi += 1;
                }
            }
            let mut out = inn.clone();
            apply_block_container(f, blk, &mut out);
            if !same_cont(&entry_cont[blk as usize], &inn) {
                entry_cont[blk as usize] = inn;
                changed = true;
            }
            if !same_cont(&exit_cont[blk as usize], &out) {
                exit_cont[blk as usize] = out;
                changed = true;
            }
            blk += 1;
        }
        if !changed {
            break;
        }
    }
    entry_cont
}

fn empty_origins(nbind: i64) -> Vec<Vec<i64>> {
    let mut out: Vec<Vec<i64>> = Vec::new();
    let mut idx = 0i64;
    while idx < nbind {
        out.push(Vec::new());
        idx += 1;
    }
    out
}

fn apply_block_origins(f: &F, block: i64, origins: &mut [Vec<i64>]) {
    let (first, last) = block_op_range(f, block);
    let mut op = first;
    while op <= last {
        let row = op_at(f, op);
        let kind = row.0;
        let binding = row.1;
        if binding >= 0 && (kind == OP_BIND || kind == OP_ASSIGN) && (row.3 == 1 || !op_loans_at(f, op).is_empty()) {
            let loans = op_loans_at(f, op);
            if let Some(slot) = origins.get_mut(binding as usize) {
                slot.clear();
                let mut j = 0usize;
                while j < loans.len() {
                    match loans.get(j) {
                        Some(loan) => slot.push(*loan),
                        None => break,
                    }
                    j += 1;
                }
            }
        }
        op += 1;
    }
}

fn origin_fixpoint(f: &F, ctx: &mut Ctx, entry: i64) -> Vec<Vec<Vec<i64>>> {
    let nblocks = f.6.len() as i64;
    let nbind = f.0.len() as i64;
    let nloans = f.3.len() as i64;
    let mut entry_origins: Vec<Vec<Vec<i64>>> = Vec::new();
    let mut exit_origins: Vec<Vec<Vec<i64>>> = Vec::new();
    let mut blk = 0i64;
    while blk < nblocks {
        entry_origins.push(empty_origins(nbind));
        exit_origins.push(empty_origins(nbind));
        blk += 1;
    }
    // Entry sets grow at most nloans times per (block, binding); exit sets snap once to a fixed loan list.
    let cap = nblocks * nbind * (nloans + 1) + 1;
    let mut guard = 0usize;
    loop {
        guard += 1;
        if guard > cap as usize {
            push_internal(ctx.3, "internal: borrow-origin analysis did not converge");
            break;
        }
        let mut changed = false;
        let mut blk = 0i64;
        while blk < nblocks {
            let mut inn = empty_origins(nbind);
            if blk != entry {
                let preds = pred_of(f, blk);
                let mut pi = 0usize;
                while pi < preds.len() {
                    match preds.get(pi) {
                        Some(p) => {
                            if let Some(list) = exit_origins.get(*p as usize) {
                                let mut bi = 0usize;
                                while bi < nbind as usize {
                                    if let (Some(dst), Some(src)) = (inn.get_mut(bi), list.get(bi)) {
                                        append_prod_unique(dst, src);
                                    }
                                    bi += 1;
                                }
                            }
                        }
                        None => break,
                    }
                    pi += 1;
                }
            }
            let mut out = inn.clone();
            apply_block_origins(f, blk, &mut out);
            let mut eq_in = true;
            let mut eq_out = true;
            let mut bi = 0usize;
            while bi < nbind as usize {
                if !same_set(&entry_origins[blk as usize][bi], &inn[bi]) {
                    eq_in = false;
                }
                if !same_set(&exit_origins[blk as usize][bi], &out[bi]) {
                    eq_out = false;
                }
                bi += 1;
            }
            if !eq_in {
                entry_origins[blk as usize] = inn;
                changed = true;
            }
            if !eq_out {
                exit_origins[blk as usize] = out;
                changed = true;
            }
            blk += 1;
        }
        if !changed {
            break;
        }
    }
    entry_origins
}

fn exit_where(kind: i64) -> &'static str {
    if kind == EX_BREAK {
        "before this break"
    } else if kind == EX_TRY {
        "on this error path"
    } else {
        "before returning"
    }
}

fn first_live_subnode(f: &F, state: &[i64], root: i64) -> i64 {
    let mut idx = 0usize;
    while idx < f.2.len() {
        let row = path_at(f, idx as i64);
        if row.2 == root && row.0 != NONE {
            let st = state_at(state, idx as i64);
            if st != ST_MOVED {
                return idx as i64;
            }
        }
        idx += 1;
    }
    NONE
}

fn first_not_live_subnode(f: &F, state: &[i64], root: i64) -> i64 {
    let mut idx = 0usize;
    while idx < f.2.len() {
        let row = path_at(f, idx as i64);
        if row.2 == root && row.0 != NONE {
            let st = state_at(state, idx as i64);
            if st == ST_MOVED || st == ST_PARTIAL {
                return idx as i64;
            }
        }
        idx += 1;
    }
    NONE
}

fn exit_check(f: &F, ctx: &mut Ctx, op: i64, state: &[i64]) {
    let row = op_at(f, op);
    let mut scope_start = row.3;
    if scope_start < 0 {
        scope_start = 0;
    }
    let kind = row.4;
    let mut bidx = scope_start;
    while bidx < f.0.len() as i64 {
        let brow = binding_at(f, bidx);
        let root = brow.6;
        let name = name_text(ctx.0, brow.0);
        if brow.2 == 1 {
            let st = state_at(state, root);
            if st == ST_LIVE {
                push_error(ctx.3, &format!("linear value '{}' must be consumed {}", name, exit_where(kind)), row.6, row.7, row.8);
                explain_unconsumed(f, ctx, bidx, &name, brow.1);
            } else if st == ST_PARTIAL {
                let live = first_live_subnode(f, state, root);
                if live != NONE {
                    let field_name = dotted_name_of(f, ctx, bidx, live);
                    push_error(ctx.3, &format!("partially moved value '{}' cannot be left behind {}: field '{}' is not fully consumed", name, exit_where(kind), field_name), row.6, row.7, row.8);
                    explain_unconsumed(f, ctx, bidx, &name, brow.1);
                }
            }
        } else if root >= 0 && ty_kind_of(ctx.1, brow.1) == TYD_REF_MUT {
            let not_live = first_not_live_subnode(f, state, root);
            if not_live != NONE {
                let field_name = dotted_name_of(f, ctx, bidx, not_live);
                push_error(ctx.3, &format!("linear field '{}' consumed through a &mut parameter is not restored {}", field_name, exit_where(kind)), row.6, row.7, row.8);
            }
        }
        bidx += 1;
    }
}

fn collect_origin_loans(f: &F, origins: &[Vec<i64>], binding: i64, out: &mut Vec<i64>, visited: &mut Vec<i64>, current_op: i64) {
    if binding < 0 || list_has(visited, binding) {
        return;
    }
    visited.push(binding);
    let mut fixed: Vec<i64> = Vec::new();
    if let Some(list) = origins.get(binding as usize) {
        let mut idx = 0usize;
        while idx < list.len() {
            match list.get(idx) {
                Some(value) => fixed.push(*value),
                None => break,
            }
            idx += 1;
        }
    }
    if fixed.is_empty() {
        let mut op = if current_op >= 0 && current_op < f.4.len() as i64 {
            current_op
        } else {
            f.4.len() as i64 - 1
        };
        while op >= 0 {
            let row = op_at(f, op);
            if row.1 == binding && (row.0 == OP_BIND || row.0 == OP_ASSIGN) && (row.3 == 1 || !op_loans_at(f, op).is_empty()) {
                let loans = op_loans_at(f, op);
                let mut li = 0usize;
                while li < loans.len() {
                    match loans.get(li) {
                        Some(value) => fixed.push(*value),
                        None => break,
                    }
                    li += 1;
                }
                break;
            }
            op -= 1;
        }
    }
    let mut idx = 0usize;
    while idx < fixed.len() {
        match fixed.get(idx) {
            Some(entry) => {
                if is_ref_origin(*entry) {
                    collect_origin_loans(f, origins, -1 - entry, out, visited, current_op);
                } else if *entry >= 0 {
                    out.push(*entry);
                }
            }
            None => break,
        }
        idx += 1;
    }
}

fn conflicts_at(f: &F, ctx: &mut Ctx, op: i64, origins: &[Vec<i64>], live_after: &[Vec<i64>]) {
    let row = op_at(f, op);
    let kind = row.0;
    if kind != OP_BORROW && kind != OP_BORROW_M && kind != OP_MOVE && kind != OP_ASSIGN {
        return;
    }
    let binding = row.1;
    if binding < 0 {
        return;
    }
    if kind == OP_ASSIGN && row.3 == 1 && row.4 == 0 {
        return;
    }
    let new_key = if kind == OP_BORROW || kind == OP_BORROW_M { row.5 } else { NONE };
    let live = match live_after.get(op as usize) {
        Some(list) => list,
        None => return,
    };
    let name = format!("{}{}", name_text(ctx.0, binding_at(f, binding).0), index_suffix(ctx, new_key));
    let mut li = 0usize;
    while li < live.len() {
        let r = match live.get(li) {
            Some(v) => *v,
            None => break,
        };
        if r == binding {
            li += 1;
            continue;
        }
        if binding_at(f, r).3 == 1 {
            let mut loans: Vec<i64> = Vec::new();
            let mut visited: Vec<i64> = Vec::new();
            collect_origin_loans(f, origins, r, &mut loans, &mut visited, op);
            let mut oi = 0usize;
            while oi < loans.len() {
                let loan = match loans.get(oi) {
                    Some(v) => *v,
                    None => break,
                };
                let lrow = loan_at(f, loan);
                if lrow.0 == binding && index_keys_conflict(ctx, new_key, lrow.3) {
                    let conflict = if kind == OP_MOVE || kind == OP_ASSIGN || kind == OP_BORROW_M {
                        true
                    } else {
                        lrow.1 == L_MUT
                    };
                    if conflict {
                        let message = if kind == OP_MOVE {
                            format!("cannot move '{}' while it is borrowed", name)
                        } else if kind == OP_ASSIGN {
                            format!("cannot assign to '{}' while it is borrowed", name)
                        } else if kind == OP_BORROW_M {
                            format!("cannot mutably borrow '{}' while it is borrowed", name)
                        } else {
                            format!("cannot borrow '{}' while it is mutably borrowed", name)
                        };
                        push_error(ctx.3, &message, row.6, row.7, row.8);
                    }
                }
                oi += 1;
            }
        }
        li += 1;
    }
}

fn trace_origin(f: &F, origins: &[Vec<i64>], loans: &[i64], sources: &mut Vec<i64>, local: &mut bool, visited: &mut Vec<i64>) {
    let mut idx = 0usize;
    while idx < loans.len() {
        let entry = match loans.get(idx) {
            Some(v) => *v,
            None => break,
        };
        if is_ref_origin(entry) {
            let binding = -1 - entry;
            if !list_has(visited, binding) {
                visited.push(binding);
                let origin = match origins.get(binding as usize) {
                    Some(list) => list.clone(),
                    None => Vec::new(),
                };
                trace_origin(f, origins, &origin, sources, local, visited);
            }
        } else {
            let lrow = loan_at(f, entry);
            let owner = lrow.0;
            if owner < 0 {
                idx += 1;
                continue;
            }
            if lrow.2 == 1 {
                append_unique(sources, owner);
            } else {
                let orow = binding_at(f, owner);
                if orow.3 == 1 && orow.4 == 1 {
                    append_unique(sources, owner);
                } else {
                    *local = true;
                }
            }
        }
        idx += 1;
    }
}

fn binding_names(ctx: &mut Ctx, f: &F, ids: &[i64]) -> String {
    let mut names: Vec<String> = Vec::new();
    let mut idx = 0usize;
    while idx < ids.len() {
        match ids.get(idx) {
            Some(binding) => names.push(name_text(ctx.0, binding_at(f, *binding).0)),
            None => break,
        }
        idx += 1;
    }
    names.join(", ")
}

fn ret_ref_check(f: &F, ctx: &mut Ctx, op: i64, origins: &[Vec<i64>]) -> Option<Vec<i64>> {
    let prod = op_loans_at(f, op);
    let mut sources: Vec<i64> = Vec::new();
    let mut local = false;
    let mut visited: Vec<i64> = Vec::new();
    trace_origin(f, origins, &prod, &mut sources, &mut local, &mut visited);
    let row = op_at(f, op);
    if local {
        push_error(ctx.3, "returned borrow does not outlive the function", row.6, row.7, row.8);
        return None;
    }
    if sources.is_empty() {
        push_error(ctx.3, "returned borrow has no traceable origin: it does not derive from any input reference parameter", row.6, row.7, row.8);
        return None;
    }
    if sources.len() > 1 {
        let names = binding_names(ctx, f, &sources);
        push_error(
            ctx.3,
            &format!("ambiguous returned borrow: it derives from more than one input reference parameter ({})", names),
            row.6,
            row.7,
            row.8,
        );
        return None;
    }
    Some(sources)
}

fn repoint_origin(f: &F, row: (i64, i64, i64, i64, i64, i64, i64, i64, i64), op: i64, origins: &mut [Vec<i64>]) {
    let kind = row.0;
    let binding = row.1;
    let is_ref_bind = kind == OP_BIND && row.3 == 1 && row.4 == 1;
    let is_ref_assign = kind == OP_ASSIGN && row.3 == 1 && row.4 == 0;
    if binding >= 0 && (is_ref_bind || is_ref_assign) {
        let loans = op_loans_at(f, op);
        if let Some(slot) = origins.get_mut(binding as usize) {
            slot.clear();
            let mut j = 0usize;
            while j < loans.len() {
                match loans.get(j) {
                    Some(loan) => slot.push(*loan),
                    None => break,
                }
                j += 1;
            }
        }
    }
}

fn compute_summary(f: &F, ctx: &mut Ctx, entry: i64, fn_node: i64) -> Option<Vec<i64>> {
    let entry_origins = origin_fixpoint(f, ctx, entry);
    let mut sources: Vec<i64> = Vec::new();
    let mut local = false;
    let mut saw_ret_ref = false;
    let nblocks = f.6.len() as i64;
    let mut blk = 0i64;
    while blk < nblocks {
        let mut origins = match entry_origins.get(blk as usize) {
            Some(list) => list.clone(),
            None => Vec::new(),
        };
        let (first, last) = block_op_range(f, blk);
        let mut op = first;
        while op <= last {
            let row = op_at(f, op);
            if row.0 == OP_BIND || row.0 == OP_ASSIGN {
                repoint_origin(f, row, op, &mut origins);
            } else if row.0 == OP_RET_REF {
                saw_ret_ref = true;
                let prod = op_loans_at(f, op);
                let mut visited: Vec<i64> = Vec::new();
                trace_origin(f, &origins, &prod, &mut sources, &mut local, &mut visited);
            }
            op += 1;
        }
        blk += 1;
    }
    if local {
        return None;
    }
    if !sources.is_empty() {
        return Some(sources);
    }
    // No returned borrow derives from an input.  For a function that
    // returns a reference and emitted no `OP_RET_REF` at all, that is not a
    // failure to trace: every one of its returns was statically rooted
    // (`static_rooted_ref`), so the result borrows nothing from the
    // arguments and outlives every caller.  Recording that as an *empty*
    // source set rather than as no summary is what lets a caller forward
    // the borrow — `fun forwarded() &[U8] return direct() end` — instead of
    // being told the origin cannot be traced.  The set only ever grows, so
    // a function that later turns out to also return an input-derived
    // borrow converges to that larger set.
    if !saw_ret_ref && returns_reference(ctx, fn_node) {
        return Some(Vec::new());
    }
    None
}

// True when a function's declared return type can carry a reference
// anywhere in its structure — the types the returned-borrow rule applies
// to, per `type_contains_ref`'s doc comment.
fn returns_reference(ctx: &mut Ctx, fn_node: i64) -> bool {
    let ret = ty_key_of(ctx.1, node_d(ctx.1, fn_node));
    let mut seen: Vec<i64> = Vec::new();
    crate::typecheck::type_contains_ref(ctx.1, ctx.2, ret, &mut seen)
}

// Summary sets only grow: each round unions the newly computed return-origin
// parameter indices into the stored set, so the call-graph iteration is
// monotone and converges without relying on the failure cap.
fn refine_summary(table: &mut Vec<(i64, Vec<i64>)>, fn_node: i64, sources: Option<Vec<i64>>) -> bool {
    let sources = match sources {
        Some(sources) => sources,
        None => return false,
    };
    let mut idx = 0usize;
    while idx < table.len() {
        match table.get(idx) {
            Some(pair) => {
                if pair.0 == fn_node {
                    break;
                }
            }
            None => break,
        }
        idx += 1;
    }
    if idx < table.len() {
        match table.get_mut(idx) {
            Some(pair) => union_values(&mut pair.1, &sources),
            None => false,
        }
    } else {
        table.push((fn_node, sources));
        true
    }
}

fn union_values(dst: &mut Vec<i64>, src: &[i64]) -> bool {
    let mut grew = false;
    let mut idx = 0usize;
    while idx < src.len() {
        match src.get(idx) {
            Some(value) => {
                if !list_has(dst, *value) {
                    dst.push(*value);
                    grew = true;
                }
            }
            None => break,
        }
        idx += 1;
    }
    grew
}

fn summary_of(table: &[(i64, Vec<i64>)], fn_node: i64) -> Option<&Vec<i64>> {
    let mut idx = 0usize;
    while idx < table.len() {
        match table.get(idx) {
            Some(pair) => {
                if pair.0 == fn_node {
                    return Some(&pair.1);
                }
            }
            None => break,
        }
        idx += 1;
    }
    None
}

// One note per predecessor of an inconsistent join, saying whether the
// value is consumed or still live where that path ends.  The states are the
// converged dataflow's own per-block exit states — the same facts the join
// compared to detect the inconsistency.
fn explain_join(f: &F, ctx: &mut Ctx, exit_states: &[Vec<i64>], join_block: i64, path: i64, name: &str) {
    let preds = pred_of(f, join_block);
    let mut pi = 0usize;
    while pi < preds.len() {
        let pred = match preds.get(pi) {
            Some(value) => *value,
            None => break,
        };
        let span = block_span_at(f, pred);
        if span.0 != NO_FILE {
            let st = match exit_states.get(pred as usize) {
                Some(list) => state_at(list, path),
                None => ST_UNBOUND,
            };
            if st == ST_MOVED || st == ST_PARTIAL {
                push_note_for_last(
                    ctx.3,
                    ctx.7,
                    &format!("'{}' is consumed by the end of this path", name),
                    span.0,
                    span.1,
                    span.2,
                    NOTE_CONSUMED,
                );
            } else if st == ST_LIVE {
                push_note_for_last(
                    ctx.3,
                    ctx.7,
                    &format!("'{}' is still live at the end of this path", name),
                    span.0,
                    span.1,
                    span.2,
                    NOTE_LIVE,
                );
            }
        }
        pi += 1;
    }
}

// A note at the binding site of a linear value an exit check found
// unconsumed, naming the linear type the typechecker attached to it.  The
// note is dropped when the binding has no source bind site (a synthesized
// entry) rather than pointing anywhere invented.
fn explain_unconsumed(f: &F, ctx: &mut Ctx, binding: i64, name: &str, ty_key: i64) {
    let bind_span = bind_span_of(f, binding);
    if bind_span.0 == NO_FILE {
        return;
    }
    let rendered = render_type_key(ctx.0, ctx.1, ctx.2, ty_key);
    push_note_for_last(
        ctx.3,
        ctx.7,
        &format!("'{}' is bound here with linear type '{}'", name, rendered),
        bind_span.0,
        bind_span.1,
        bind_span.2,
        NOTE_BINDING,
    );
}

// The source span of the OP_BIND that introduced a binding, or a
// source-less span when the binding has no bind op (a synthesized entry).
fn bind_span_of(f: &F, binding: i64) -> (i64, i64, i64) {
    let mut op = 0i64;
    while op < f.4.len() as i64 {
        let row = op_at(f, op);
        if row.0 == OP_BIND && row.1 == binding {
            return (row.6, row.7, row.8);
        }
        op += 1;
    }
    (NO_FILE, 0, 0)
}

fn empty_spans(count: i64) -> Vec<(i64, i64, i64)> {
    let mut out: Vec<(i64, i64, i64)> = Vec::new();
    let mut idx = 0i64;
    while idx < count {
        out.push((NO_FILE, 0, 0));
        idx += 1;
    }
    out
}

fn span_cell(spans: &[(i64, i64, i64)], path: i64) -> (i64, i64, i64) {
    match spans.get(path as usize) {
        Some(span) => *span,
        None => (NO_FILE, 0, 0),
    }
}

fn span_cell_set(spans: &mut [(i64, i64, i64)], path: i64, span: (i64, i64, i64)) {
    if path < 0 {
        return;
    }
    if let Some(cell) = spans.get_mut(path as usize) {
        *cell = span;
    }
}

fn report(
    f: &F,
    ctx: &mut Ctx,
    live_after: &[Vec<i64>],
    flow: &LinearFlow,
    entry_origins: &[Vec<Vec<i64>>],
    entry_cont: &[Vec<i64>],
) {
    let (entry_state, exit_states, inconsistencies) = flow;
    let mut idx = 0usize;
    while idx < inconsistencies.len() {
        match inconsistencies.get(idx) {
            Some(pair) => {
                let path = pair.1;
                let root = path_at(f, path).2;
                let mut name = String::new();
                let mut bidx = 0i64;
                while bidx < f.0.len() as i64 {
                    if root_path_of(f, bidx) == root {
                        name = name_text(ctx.0, binding_at(f, bidx).0);
                        break;
                    }
                    bidx += 1;
                }
                let span = block_span_at(f, pair.0);
                push_error(
                    ctx.3,
                    &format!("linear value '{}' is consumed on some paths but not on all paths", name),
                    span.0,
                    span.1,
                    span.2,
                );
                explain_join(f, ctx, exit_states, pair.0, path, &name);
            }
            None => break,
        }
        idx += 1;
    }
    let mut fn_ret_sources: Vec<i64> = Vec::new();
    let mut fn_ret_errored = false;
    let nblocks = f.6.len() as i64;
    let npaths = f.2.len() as i64;
    let mut blk = 0i64;
    while blk < nblocks {
        let mut state = match entry_state.get(blk as usize) {
            Some(list) => list.clone(),
            None => Vec::new(),
        };
        let mut origins = match entry_origins.get(blk as usize) {
            Some(list) => list.clone(),
            None => Vec::new(),
        };
        let mut cont = match entry_cont.get(blk as usize) {
            Some(list) => list.clone(),
            None => Vec::new(),
        };
        // The span of the move that most recently consumed each path within
        // this block's replay.  Same-block only: a value moved by an earlier
        // block has no single unambiguous "moved here" site (the CFG may
        // join several), so no note is invented for it.
        let mut last_move = empty_spans(npaths);
        let (first, last) = block_op_range(f, blk);
        let mut op = first;
        while op <= last {
            let row = op_at(f, op);
            let kind = row.0;
            let binding = row.1;
            if kind == OP_BIND {
                repoint_origin(f, row, op, &mut origins);
                if binding >= 0 && root_path_of(f, binding) != NONE {
                    bind_state_live(f, &mut state, binding);
                }
            } else if kind == OP_MOVE {
                conflicts_at(f, ctx, op, &origins, live_after);
                let prev = state_at(&state, row.2);
                apply_move(f, &mut state, binding, row.2, true, ctx, (row.6, row.7, row.8));
                if prev == ST_MOVED || prev == ST_PARTIAL {
                    let moved_at = span_cell(&last_move, row.2);
                    if moved_at.0 != NO_FILE {
                        let name = dotted_name_of(f, ctx, binding, row.2);
                        push_note_for_last(
                            ctx.3,
                            ctx.7,
                            &format!("'{}' was moved here", name),
                            moved_at.0,
                            moved_at.1,
                            moved_at.2,
                            NOTE_MOVED,
                        );
                    }
                } else if prev == ST_LIVE {
                    span_cell_set(&mut last_move, row.2, (row.6, row.7, row.8));
                }
            } else if kind == OP_ASSIGN {
                if row.3 == 1 && row.4 == 0 && binding >= 0 {
                    repoint_origin(f, row, op, &mut origins);
                } else {
                    conflicts_at(f, ctx, op, &origins, live_after);
                }
                let tkind = row.4;
                if tkind == 1 && row.5 >= 0 && root_path_of(f, row.5) != NONE {
                    apply_assign(f, &mut state, row.5, row.2, true, ctx, (row.6, row.7, row.8));
                } else if tkind != 1 && binding >= 0 && root_path_of(f, binding) != NONE {
                    let path = if tkind == 2 { row.2 } else { NONE };
                    apply_assign(f, &mut state, binding, path, true, ctx, (row.6, row.7, row.8));
                }
            } else if kind == OP_BORROW || kind == OP_BORROW_M {
                conflicts_at(f, ctx, op, &origins, live_after);
                borrow_after_move_check(f, &state, binding, row.2, ctx, (row.6, row.7, row.8));
            } else if kind == OP_EXIT {
                exit_check(f, ctx, op, &state);
            } else if kind == OP_RET_REF {
                match ret_ref_check(f, ctx, op, &origins) {
                    Some(sources) => append_prod_unique(&mut fn_ret_sources, &sources),
                    None => fn_ret_errored = true,
                }
            } else if kind == OP_CONT_EMPTY {
                cont_set(&mut cont, binding, C_EMPTY);
            } else if kind == OP_CONT_MAY {
                cont_set(&mut cont, binding, C_MAY);
            } else if kind == OP_CONT_FREE
                && cont_get(&cont, binding) == C_MAY
            {
                push_error(
                    ctx.3,
                    "cannot free container holding linear elements: drain the container (pop all elements) before freeing",
                    row.6,
                    row.7,
                    row.8,
                );
                let binding_row = binding_at(f, binding);
                let name = name_text(ctx.0, binding_row.0);
                explain_unconsumed(f, ctx, binding, &name, binding_row.1);
                let bind_span = bind_span_of(f, binding);
                if bind_span.0 != NO_FILE {
                    push_note_for_last(
                        ctx.3,
                        ctx.7,
                        "extract every linear element through the container's native extraction operation before freeing it",
                        bind_span.0,
                        bind_span.1,
                        bind_span.2,
                        NOTE_GUIDANCE,
                    );
                }
            }
            op += 1;
        }
        blk += 1;
    }
    if !fn_ret_errored && fn_ret_sources.len() > 1 {
        let fn_span = block_span_at(f, 0);
        let names = binding_names(ctx, f, &fn_ret_sources);
        push_error(
            ctx.3,
            &format!("ambiguous returned borrow: function returns a reference deriving from more than one input reference parameter ({})", names),
            fn_span.0,
            fn_span.1,
            fn_span.2,
        );
    }
}

#[cfg(test)]
mod tests {
    // Drives the real front end (module loading through borrow checking,
    // the same path `analysis::analyze` gives the LSP and the playground)
    // over an in-memory source, with no LLVM dependency — the only way to
    // pin borrow-checker behavior end to end on a machine without the LLVM
    // toolchain `cargo test`'s fixture-linked suites need.
    fn errors_for(source: &str) -> Vec<String> {
        let overlay = [("scratch.cnb".to_string(), source.to_string())];
        let result = crate::analysis::analyze("scratch.cnb", &overlay);
        result.errors.iter().map(|d| d.0.clone()).collect()
    }

    // Pins the fix to `walk_field_chain`: a field-chain borrow (`&s.b`) used
    // to be emitted with path NONE, so `borrow_after_move_check` could never
    // see it and a borrow of an already-moved field compiled cleanly into a
    // real use-after-free.
    #[test]
    fn field_borrow_after_move_is_rejected() {
        let source = r#"
pub mod Memory
  pub nat type Block
  pub type Error
    pub AllocationFailed(Usize)
  end
  pub nat fun allocate(size: Usize) impure Result(Block, Error)
  pub nat fun deallocate(block: Block) impure Unit
  pub nat fun touch(block: &Block) impure Unit
end

use Memory.allocate
use Memory.deallocate
use Memory.touch

pub type Holder
  pub block: Memory.Block
  pub tag: I64
end

pub fun main() impure I64
  val block = match allocate(1)
    Ok(value) => value
    Err(error) => return 1
  end
  var holder = Holder(block: block, tag: 7)
  deallocate(holder.block)
  touch(&holder.block)
  return 0
end
"#;
        let errors = errors_for(source);
        assert!(errors.iter().any(|m| m.contains("use of moved value")));
    }

    // Same fix, the other trigger shape from the same finding: the whole
    // struct moved by value (not just one field), then a field of it
    // borrowed. `mark_descendants` already marks every child path MOVED
    // when the root moves, so this only needed the path to reach
    // `borrow_after_move_check` at all.
    #[test]
    fn field_borrow_after_whole_struct_moved_is_rejected() {
        let source = r#"
pub mod Memory
  pub nat type Block
  pub type Error
    pub AllocationFailed(Usize)
  end
  pub nat fun allocate(size: Usize) impure Result(Block, Error)
  pub nat fun deallocate(block: Block) impure Unit
  pub nat fun touch(block: &Block) impure Unit
end

use Memory.allocate
use Memory.deallocate
use Memory.touch

pub type Holder
  pub block: Memory.Block
  pub tag: I64
end

fun consume(holder: Holder) impure Unit
  deallocate(holder.block)
  return Unit
end

pub fun main() impure I64
  val block = match allocate(1)
    Ok(value) => value
    Err(error) => return 1
  end
  val holder = Holder(block: block, tag: 7)
  consume(holder)
  touch(&holder.block)
  return 0
end
"#;
        let errors = errors_for(source);
        assert!(errors.iter().any(|m| m.contains("use of moved value")));
    }

    // Negative control for both fixes above: borrowing a field before it is
    // moved, and moving it after the borrow's last use, must stay accepted.
    #[test]
    fn field_borrow_before_move_is_still_accepted() {
        let source = r#"
pub mod Memory
  pub nat type Block
  pub type Error
    pub AllocationFailed(Usize)
  end
  pub nat fun allocate(size: Usize) impure Result(Block, Error)
  pub nat fun deallocate(block: Block) impure Unit
  pub nat fun touch(block: &Block) impure Unit
end

use Memory.allocate
use Memory.deallocate
use Memory.touch

pub type Holder
  pub block: Memory.Block
  pub tag: I64
end

pub fun main() impure I64
  val block = match allocate(1)
    Ok(value) => value
    Err(error) => return 1
  end
  var holder = Holder(block: block, tag: 7)
  touch(&holder.block)
  deallocate(holder.block)
  return 0
end
"#;
        let errors = errors_for(source);
        assert!(errors.is_empty());
    }

    // Pins the fix to the returned-borrow obligation: it used to apply only
    // when the declared return type's own kind was bare `&T`/`&mut T`/
    // `&[T]`, so a function returning `Result(&T, E)` (or any other
    // reference-carrying aggregate) could return a dangling borrow of a
    // local with no diagnostic at all. `type_contains_ref` makes the check
    // apply to the wrapped shape too.
    #[test]
    fn dangling_borrow_wrapped_in_result_is_rejected() {
        let source = r#"
pub type LookupError
  pub OutOfBounds
end

fun dangling() Result(&I64, LookupError)
  val a: [I64; 3] = [1, 2, 3]
  return Ok(&a[0])
end

pub fun main() I64
  match dangling()
    Ok(value) => Unit
    Err(error) => Unit
  end
  return 0
end
"#;
        let errors = errors_for(source);
        assert!(errors.iter().any(|m| m.contains("returned borrow") || m.contains("does not outlive")));
    }

    const CONTAINER_NATIVES: &str = r#"
pub mod Memory
  pub nat type Block
  pub type Error
    pub AllocationFailed(Usize)
  end
  pub nat fun allocate(size: Usize) impure Result(Block, Error)
  pub nat fun deallocate(block: Block) impure Unit
end

pub mod Collections
  pub nat type Vec(T)
  pub type Error
    pub AllocationFailed(Usize)
    pub IndexOutOfBounds(Usize)
  end
  pub nat fun vec_new<T>() impure Result(Vec(T), Error)
  pub nat fun vec_push<T>(vec: &mut Vec(T), value: T) impure Result(Unit, Error)
  pub nat fun vec_pop<T>(vec: &mut Vec(T)) impure Result(T, Error)
  pub nat fun vec_free<T>(vec: Vec(T)) impure Unit
end

use Collections.vec_new
use Collections.vec_free
"#;

    // Trimmed to only vec_new/vec_free: a test that never touches
    // allocate/deallocate/vec_push/vec_pop can't import them either, since
    // an import nothing calls is now itself rejected, and an import-free
    // `nat fun` a nothing calls is unreachable from main -- exactly the
    // cascade documented on resolver::tests::fixture_corpus_stays_clean_of_
    // dead_imports.
    const MINIMAL_CONTAINER_NATIVES: &str = r#"
pub mod Memory
  pub nat type Block
end

pub mod Collections
  pub nat type Vec(T)
  pub type Error
    pub AllocationFailed(Usize)
    pub IndexOutOfBounds(Usize)
  end
  pub nat fun vec_new<T>() impure Result(Vec(T), Error)
  pub nat fun vec_free<T>(vec: Vec(T)) impure Unit
end

use Collections.vec_new
use Collections.vec_free
"#;

    // Trimmed to vec_new/vec_pop/vec_free/deallocate, for a test that
    // extracts and consumes an element but never refills the container.
    const POP_CONTAINER_NATIVES: &str = r#"
pub mod Memory
  pub nat type Block
  pub nat fun deallocate(block: Block) impure Unit
end

pub mod Collections
  pub nat type Vec(T)
  pub type Error
    pub AllocationFailed(Usize)
    pub IndexOutOfBounds(Usize)
  end
  pub nat fun vec_new<T>() impure Result(Vec(T), Error)
  pub nat fun vec_pop<T>(vec: &mut Vec(T)) impure Result(T, Error)
  pub nat fun vec_free<T>(vec: Vec(T)) impure Unit
end

use Collections.vec_new
use Collections.vec_free
"#;

    // Pins the fix to the stale-extraction-fact leak: `b.8` recorded that
    // `popped` came from popping `v`, and nothing invalidated that record
    // when `v` was refilled before the match on `popped` read it — so the
    // match's Err arm still (wrongly) proved `v` drained, and `vec_free(v)`
    // afterward leaked whatever the intervening push added.
    #[test]
    fn refilling_a_container_after_an_extraction_forgets_the_extraction_proved_it_empty() {
        let source = format!(
            "{}
pub fun main() impure I64
  var v = match vec_new[Memory.Block]()
    Ok(value) => value
    Err(error) => return 1
  end
  val popped = Collections.vec_pop(&mut v)
  val block = match Memory.allocate(1)
    Ok(value) => value
    Err(error) => return 2
  end
  match Collections.vec_push(&mut v, block)
    Ok(Unit) => Unit
    Err(error) => Unit
  end
  match popped
    Ok(elem) => Memory.deallocate(elem)
    Err(error) => Unit
  end
  vec_free(v)
  return 0
end
",
            CONTAINER_NATIVES
        );
        let errors = errors_for(&source);
        assert!(errors.iter().any(|m| m.contains("cannot free container holding linear elements")), "{:?}", errors);
    }

    // Same category, the `b.9` half: `w` moved from `v`, which was fresh
    // from `vec_new` when it was created but had since been refilled — `w`
    // must not inherit `v`'s stale "provably empty" fact.
    #[test]
    fn moving_a_refilled_container_forgets_it_was_ever_provably_empty() {
        let source = format!(
            "{}
pub fun main() impure I64
  var v = match vec_new[Memory.Block]()
    Ok(value) => value
    Err(error) => return 1
  end
  val block = match Memory.allocate(1)
    Ok(value) => value
    Err(error) => return 2
  end
  match Collections.vec_push(&mut v, block)
    Ok(Unit) => Unit
    Err(error) => Unit
  end
  val w = v
  vec_free(w)
  return 0
end
",
            CONTAINER_NATIVES
        );
        let errors = errors_for(&source);
        assert!(errors.iter().any(|m| m.contains("cannot free container holding linear elements")), "{:?}", errors);
    }

    // Negative control for both fixes above: a container that is genuinely
    // never refilled must still free cleanly.
    #[test]
    fn freeing_a_container_that_was_never_refilled_is_still_accepted() {
        let source = format!(
            "{}
pub fun main() impure I64
  var v = match vec_new[Memory.Block]()
    Ok(value) => value
    Err(error) => return 1
  end
  val popped = Collections.vec_pop(&mut v)
  match popped
    Ok(elem) => Memory.deallocate(elem)
    Err(error) => Unit
  end
  vec_free(v)
  return 0
end
",
            POP_CONTAINER_NATIVES
        );
        let errors = errors_for(&source);
        assert!(errors.is_empty(), "{:?}", errors);
    }

    // Pins the fix to the anonymous-free hole: `vec_free`'s argument was a
    // call result rather than a named binding, so `container_binding_of`
    // returned NONE and the drain check — keyed entirely on a binding —
    // never ran at all, silently accepting a leak of every element the
    // returned vec held.
    #[test]
    fn freeing_an_unresolvable_container_expression_is_rejected() {
        let source = format!(
            "{}
fun make_full_vec() impure Collections.Vec(Memory.Block)
  return match vec_new[Memory.Block]()
    Ok(v) => v
    Err(error) => make_full_vec()
  end
end

pub fun main() impure I64
  vec_free(make_full_vec())
  return 0
end
",
            CONTAINER_NATIVES
        );
        let errors = errors_for(&source);
        assert!(errors.iter().any(|m| m.contains("cannot free container holding linear elements")), "{:?}", errors);
    }

    // Negative control: a directly-freed anonymous expression that IS
    // provably fresh (a create call itself, not wrapped in a user function)
    // must still be accepted -- create_provenance recognizes it same as it
    // would for a `let` binding.
    #[test]
    fn freeing_a_directly_provably_fresh_container_is_still_accepted() {
        let source = format!(
            "{}
pub fun main() impure I64
  match vec_new[Memory.Block]()
    Ok(v) => vec_free(v)
    Err(error) => Unit
  end
  return 0
end
",
            MINIMAL_CONTAINER_NATIVES
        );
        let errors = errors_for(&source);
        assert!(errors.is_empty(), "{:?}", errors);
    }
}
