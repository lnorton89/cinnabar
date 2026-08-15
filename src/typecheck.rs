//! Type checking, constant evaluation, and fact attachment.
//!
//! `typecheck` runs as an explicit sequence of sub-passes over one shared
//! `State` — collect types, check function signatures, collect consts, then
//! check function bodies including generic ones. Typing is structural and
//! unification-free, keyed by canonical **type keys**: `TYD_*` rows
//! interned and deduplicated through `canon_tyinfo`, with generic
//! substitution implemented once in `subst_key`/`subst_list` and reused,
//! rather than rewritten per call site.
//!
//! This is the stage that computes what the rest of the compiler consumes,
//! which is why it is the largest file in the tree. Enum variant tags
//! (`NODE_VARFACT`), struct field offsets (`NODE_FIELDKEY`), trait dispatch
//! targets (`NODE_TRAIT`), and one `NODE_INST` per instantiated generic are
//! all established here. So is linearity: every type key is marked linear
//! or not — a native handle by declaration, an aggregate if any member is,
//! and a bare type parameter conservatively, since its instantiation is
//! unknown at definition time and requiring exactly-once consumption is the
//! only sound default.
//!
//! The arithmetic rules live here too. `/` and `%` reject a provably-zero
//! divisor and are otherwise typed `Result(T, DivError)` with Euclidean
//! semantics; a compile-time-constant array index is range-checked and
//! typed as the bare element type, while a runtime or slice index is
//! `Result(T, IndexError)`; no operator admits an implicit conversion, the
//! sole sanctioned coercion being `&[T; N]` to `&[T]`. An integer literal
//! is not yet a value of any type and adopts one from context; a string
//! literal adopts nothing and is `&[U8]`.
//!
//! **Invariants:**
//! - A type is decided here once. The borrow checker and codegen read the
//!   attached canonical key; neither re-infers one of its own.
//! - Linearity is a property of a type key, stored on the type descriptor
//!   row itself — never a name-keyed side table, and never re-derived
//!   downstream by asking what a type is called.
//! - The literal-adoption rule is implemented in one place
//!   (`int_literal_expr`/`binary_operand_expected`) and called by both
//!   `check_binary` and the constant folder, so the same literal text
//!   cannot type one way in a `const` and another in a `var`.

use crate::ast::*;
use crate::resolver::NS_VALUE;
use crate::suggest;

const IMPL_STRIDE: i64 = 3;

type State<'a> = (
    &'a mut Vec<String>,
    &'a mut Vec<i64>,
    &'a mut Vec<Vec<i64>>,
    &'a mut Vec<Diag>,
    &'a mut Vec<Vec<i64>>,
    &'a mut Vec<i64>,
    &'a mut Vec<(i64, i64)>,
    &'a mut Vec<(i64, i64, i64)>,
    i64,
    i64,
    i64,
    i64,
    i64,
    i64,
    i64,
    &'a mut Vec<bool>,
    // Secondary notes tied to the errors this stage reports (definition-site
    // labels and hedged name suggestions), indexed like the borrow checker's.
    &'a mut Vec<Note>,
    // The return-type node of the function currently being checked, so a
    // return-type mismatch can label the declaration it violates.
    i64,
);

pub fn typecheck(
    names: &mut Vec<String>,
    nodes: &mut Vec<i64>,
    lists: &mut Vec<Vec<i64>>,
    errors: &mut Vec<Diag>,
    notes: &mut Vec<Note>,
    root: i64,
    ext_mods: &[(i64, i64)],
) -> (bool, i64) {
    seed_builtins(names, nodes, lists);
    let unit_sym = find_type_sym_by_name(nodes, intern(names, "Unit"));
    let result_sym = find_type_sym_by_name(nodes, intern(names, "Result"));
    let option_sym = find_type_sym_by_name(nodes, intern(names, "Option"));
    let div_err_sym = find_type_sym_by_name(nodes, intern(names, "DivError"));
    let index_err_sym = find_type_sym_by_name(nodes, intern(names, "IndexError"));
    let mut impls: Vec<i64> = Vec::new();
    let mut vars: Vec<(i64, i64)> = Vec::new();
    let mut origins: Vec<(i64, i64, i64)> = Vec::new();
    let mut env: Vec<Vec<i64>> = Vec::new();
    let mut local_fact_sources = vec![false; nodes.len() / NODE_STRIDE as usize];
    push_scope(&mut env);
    let mut state: State = (
        names,
        nodes,
        lists,
        errors,
        &mut env,
        &mut impls,
        &mut vars,
        &mut origins,
        unit_sym,
        result_sym,
        option_sym,
        div_err_sym,
        index_err_sym,
        0,
        0,
        &mut local_fact_sources,
        notes,
        0,
    );

    collect_types(&mut state, root);
    let mut idx = 0usize;
    while idx < ext_mods.len() {
        match ext_mods.get(idx) {
            Some(pair) => collect_types(&mut state, pair.1),
            None => break,
        }
        idx += 1;
    }

    check_fn_sigs_list(&mut state, root);
    idx = 0;
    while idx < ext_mods.len() {
        match ext_mods.get(idx) {
            Some(pair) => check_fn_sigs_list(&mut state, pair.1),
            None => break,
        }
        idx += 1;
    }

    collect_consts(&mut state, root);
    idx = 0;
    while idx < ext_mods.len() {
        match ext_mods.get(idx) {
            Some(pair) => collect_consts(&mut state, pair.1),
            None => break,
        }
        idx += 1;
    }

    collect_impls(&mut state, root);
    idx = 0;
    while idx < ext_mods.len() {
        match ext_mods.get(idx) {
            Some(pair) => collect_impls(&mut state, pair.1),
            None => break,
        }
        idx += 1;
    }

    check_fn_list(&mut state, root);
    idx = 0;
    while idx < ext_mods.len() {
        match ext_mods.get(idx) {
            Some(pair) => check_fn_list(&mut state, pair.1),
            None => break,
        }
        idx += 1;
    }

    let impls_list = store_impls(state.2, state.5);
    pop_scope(state.4);
    resolve_all_vars(state.0, state.1, state.2, state.3, state.6, state.7);
    attach_type_facts(state.1, state.2);
    (state.3.is_empty(), impls_list)
}

fn impl_at(impls: &[i64], idx: usize) -> i64 {
    match impls.get(idx) {
        Some(value) => *value,
        None => NONE,
    }
}

fn store_impls(lists: &mut Vec<Vec<i64>>, impls: &[i64]) -> i64 {
    let list = alloc_list(lists);
    let mut idx = 0i64;
    while idx < impls.len() as i64 / IMPL_STRIDE {
        list_push(lists, list, impl_at(impls, (idx * IMPL_STRIDE) as usize));
        list_push(lists, list, impl_at(impls, (idx * IMPL_STRIDE + 1) as usize));
        list_push(lists, list, impl_at(impls, (idx * IMPL_STRIDE + 2) as usize));
        idx += 1;
    }
    list
}

fn sym_kind(nodes: &[i64], sym: i64) -> i64 {
    node_a(nodes, sym)
}

fn sym_name(nodes: &[i64], sym: i64) -> i64 {
    node_b(nodes, sym)
}

fn sym_decl(nodes: &[i64], sym: i64) -> i64 {
    node_c(nodes, sym)
}

fn sym_home(nodes: &[i64], sym: i64) -> i64 {
    node_d(nodes, sym)
}

fn builtin_key_of(nodes: &[i64], sub: i64) -> i64 {
    let mut idx = 0i64;
    while idx < nodes.len() as i64 / NODE_STRIDE {
        if node_tag(nodes, idx) == NODE_TYINFO && node_b(nodes, idx) == TYD_BUILTIN && node_f(nodes, idx) == sub {
            return node_a(nodes, idx);
        }
        idx += 1;
    }
    NONE
}

fn builtin_key_of_sym(nodes: &[i64], sym: i64) -> i64 {
    let mut idx = 0i64;
    while idx < nodes.len() as i64 / NODE_STRIDE {
        if node_tag(nodes, idx) == NODE_TYINFO && node_b(nodes, idx) == TYD_BUILTIN && node_c(nodes, idx) == sym {
            return node_a(nodes, idx);
        }
        idx += 1;
    }
    NONE
}

fn seed_builtins(names: &mut Vec<String>, nodes: &mut Vec<i64>, lists: &mut [Vec<i64>]) {
    let ints = [
        (intern(names, "I8"), BUILTIN_I8),
        (intern(names, "I16"), BUILTIN_I16),
        (intern(names, "I32"), BUILTIN_I32),
        (intern(names, "I64"), BUILTIN_I64),
        (intern(names, "Isize"), BUILTIN_ISIZE),
        (intern(names, "U8"), BUILTIN_U8),
        (intern(names, "U16"), BUILTIN_U16),
        (intern(names, "U32"), BUILTIN_U32),
        (intern(names, "U64"), BUILTIN_U64),
        (intern(names, "Usize"), BUILTIN_USIZE),
    ];
    let mut idx = 0usize;
    while idx < ints.len() {
        let (name_id, sub) = match ints.get(idx) {
            Some(pair) => *pair,
            None => break,
        };
        seed_builtin(nodes, lists, name_id, sub);
        idx += 1;
    }
    let bool_name = intern(names, "Bool");
    seed_builtin(nodes, lists, bool_name, BUILTIN_BOOL);
}

fn seed_builtin(nodes: &mut Vec<i64>, lists: &mut [Vec<i64>], name: i64, sub: i64) {
    let sym = find_type_sym_by_name(nodes, name);
    if sym != NONE {
        canon_tyinfo(nodes, lists, TYD_BUILTIN, sym, NONE, NONE, sub);
    }
}

fn find_type_sym_by_name(nodes: &[i64], name: i64) -> i64 {
    let mut idx = 0i64;
    while idx < nodes.len() as i64 / NODE_STRIDE {
        if node_tag(nodes, idx) == NODE_SYM {
            let kind = node_a(nodes, idx);
            if (kind == SYM_TYPE || kind == SYM_STRUCT || kind == SYM_ENUM || kind == SYM_TRAIT)
                && node_b(nodes, idx) == name
            {
                return idx;
            }
        }
        idx += 1;
    }
    NONE
}

fn push_scope(env: &mut Vec<Vec<i64>>) {
    env.push(Vec::new());
}

fn pop_scope(env: &mut Vec<Vec<i64>>) {
    env.pop();
}

fn entry_at(scope: &[i64], idx: i64, slot: i64) -> i64 {
    match scope.get((idx * 4 + slot) as usize) {
        Some(value) => *value,
        None => NONE,
    }
}

fn bind(env: &mut [Vec<i64>], name: i64, key: i64, is_mut: i64, decl: i64) {
    if let Some(scope) = env.last_mut() {
        scope.push(name);
        scope.push(key);
        scope.push(is_mut);
        scope.push(decl);
    }
}

fn lookup(env: &[Vec<i64>], name: i64) -> (i64, i64) {
    let full = lookup_full(env, name);
    (full.0, full.1)
}

fn lookup_full(env: &[Vec<i64>], name: i64) -> (i64, i64, i64) {
    let mut depth = env.len();
    while depth > 0 {
        depth -= 1;
        match env.get(depth) {
            Some(scope) => {
                let mut idx = 0i64;
                while idx < scope.len() as i64 / 4 {
                    if entry_at(scope, idx, 0) == name {
                        return (entry_at(scope, idx, 1), entry_at(scope, idx, 2), entry_at(scope, idx, 3));
                    }
                    idx += 1;
                }
            }
            None => break,
        }
    }
    (NONE, 0, NONE)
}

fn attach_local_facts(state: &mut State, source: i64) {
    if source < 0 {
        return;
    }
    let already_attached = match state.15.get_mut(source as usize) {
        Some(attached) => {
            if *attached {
                true
            } else {
                *attached = true;
                false
            }
        }
        None => return,
    };
    if already_attached {
        return;
    }
    let mut facts: Vec<(i64, i64, i64)> = Vec::new();
    let mut depth = state.4.len();
    while depth > 0 {
        depth -= 1;
        match state.4.get(depth) {
            Some(scope) => {
                let mut idx = 0i64;
                while idx < scope.len() as i64 / 4 {
                    let name = entry_at(scope, idx, 0);
                    let mut shadowed = false;
                    let mut fact_idx = 0usize;
                    while fact_idx < facts.len() {
                        match facts.get(fact_idx) {
                            Some(fact) => {
                                if fact.0 == name {
                                    shadowed = true;
                                    break;
                                }
                            }
                            None => break,
                        }
                        fact_idx += 1;
                    }
                    if !shadowed {
                        facts.push((name, entry_at(scope, idx, 1), entry_at(scope, idx, 2)));
                    }
                    idx += 1;
                }
            }
            None => break,
        }
    }
    let mut idx = 0usize;
    while idx < facts.len() {
        match facts.get(idx) {
            Some(fact) => {
                alloc_localfact(state.1, source, fact.0, fact.1, fact.2);
            }
            None => break,
        }
        idx += 1;
    }
}

fn is_var(key: i64) -> bool {
    key < NONE
}

fn resolve_var(vars: &[(i64, i64)], var: i64) -> i64 {
    let mut current = var;
    let cap = vars.len() + 1;
    let mut guard = 0usize;
    loop {
        guard += 1;
        if guard > cap {
            return current;
        }
        let mut bound = current;
        let mut found = false;
        let mut idx = 0usize;
        while idx < vars.len() {
            match vars.get(idx) {
                Some(pair) => {
                    if pair.0 == current {
                        bound = pair.1;
                        found = true;
                    }
                }
                None => break,
            }
            idx += 1;
        }
        if !found || bound == current {
            return current;
        }
        if is_var(bound) {
            current = bound;
        } else {
            return bound;
        }
    }
}

fn bind_var(vars: &mut [(i64, i64)], var: i64, key: i64) {
    let mut idx = 0usize;
    while idx < vars.len() {
        match vars.get_mut(idx) {
            Some(pair) => {
                if pair.0 == var {
                    pair.1 = key;
                    return;
                }
            }
            None => break,
        }
        idx += 1;
    }
}

fn fresh_var(vars: &mut Vec<(i64, i64)>, origins: &mut Vec<(i64, i64, i64)>, expr: i64, name: i64) -> i64 {
    let var = -(vars.len() as i64) - 2;
    vars.push((var, var));
    origins.push((var, expr, name));
    var
}

fn param_decl_key(nodes: &mut Vec<i64>, lists: &mut [Vec<i64>], owner: i64, name: i64, bound: i64) -> i64 {
    canon_tyinfo(nodes, lists, TYD_PARAM, name, NONE, owner, bound)
}

fn bind_type_params(nodes: &mut Vec<i64>, lists: &mut [Vec<i64>], env: &mut [Vec<i64>], owner: i64, params: i64) {
    let count = list_len(lists, params);
    let mut idx = 0i64;
    while idx < count {
        let param = list_get(lists, params, idx);
        if node_tag(nodes, param) == NODE_TY && node_a(nodes, param) == TY_PARAM {
            let name = node_b(nodes, param);
            let bound = node_c(nodes, param);
            let key = param_decl_key(nodes, lists, owner, name, bound);
            ty_set_key(nodes, param, key);
            bind(env, name, key, 0, NONE);
        }
        idx += 1;
    }
}

fn declared_param_count(nodes: &[i64], lists: &[Vec<i64>], item: i64) -> i64 {
    if node_a(nodes, item) == ITEM_NATIVE_TYPE {
        list_len(lists, node_e(nodes, item))
    } else {
        list_len(lists, node_f(nodes, item))
    }
}

fn declared_param_keys(nodes: &[i64], lists: &[Vec<i64>], item: i64) -> Vec<i64> {
    let params = if node_a(nodes, item) == ITEM_NATIVE_TYPE {
        node_e(nodes, item)
    } else {
        node_f(nodes, item)
    };
    let mut keys: Vec<i64> = Vec::new();
    let count = list_len(lists, params);
    let mut idx = 0i64;
    while idx < count {
        let param = list_get(lists, params, idx);
        if node_tag(nodes, param) == NODE_TY && node_a(nodes, param) == TY_PARAM {
            keys.push(ty_key_of(nodes, param));
        }
        idx += 1;
    }
    keys
}

fn named_key(names: &[String], nodes: &mut Vec<i64>, lists: &mut [Vec<i64>], errors: &mut Vec<Diag>, sym: i64, span: (i64, i64, i64)) -> i64 {
    let (file, start, end) = span;
    let kind = sym_kind(nodes, sym);
    if kind == SYM_TYPE {
        let decl = sym_decl(nodes, sym);
        if decl == NONE {
            return builtin_key_of_sym(nodes, sym);
        }
        if declared_param_count(nodes, lists, decl) > 0 {
            push_error(errors, &format!("type '{}' requires type arguments", name_text(names, sym_name(nodes, sym))), file, start, end);
            return unknown_key(nodes, lists);
        }
        return canon_tyinfo(nodes, lists, TYD_NATIVE, sym, NONE, NONE, NONE);
    }
    let kind_of = if kind == SYM_STRUCT { TYD_STRUCT } else { TYD_ENUM };
    let decl = sym_decl(nodes, sym);
    if declared_param_count(nodes, lists, decl) > 0 {
        push_error(errors, &format!("type '{}' requires type arguments", name_text(names, sym_name(nodes, sym))), file, start, end);
        return unknown_key(nodes, lists);
    }
    canon_tyinfo(nodes, lists, kind_of, sym, NONE, NONE, NONE)
}

fn unknown_key(nodes: &mut Vec<i64>, lists: &mut [Vec<i64>]) -> i64 {
    canon_tyinfo(nodes, lists, TYD_UNKNOWN, NONE, NONE, NONE, NONE)
}

// The centralized error-recovery rule: whenever an expression, constant
// evaluation, or pattern fails semantically and its primary diagnostic has
// been emitted, its type key recovers to the expected key when one is
// known, or to TYD_UNKNOWN otherwise, and is attached to the failing node
// so no downstream unification site can produce a cascading "found '?'"
// secondary.  Every expression, constant, and pattern checker routes its
// error returns through this single function; no sub-checker invents its
// own error key.
//
// The attach is guarded to expression and pattern nodes that carry no type
// yet: a node's type is a single fact computed by its checker, and a quiet
// constant probe (fold_const with quiet = 1) must never clobber the real
// type the checker already attached (an index expression probed for
// constant folding keeps its Usize type).  The nodes that reach recovery
// untyped are exactly the ones whose checker failed, so the attach always
// lands on the failing node; other inputs (invariant failures) get the
// recovered key without a node write.
fn recover_ty(state: &mut State, node: i64, expected: i64) -> i64 {
    let key = if expected != NONE {
        expected
    } else {
        unknown_key(state.1, state.2)
    };
    let tag = node_tag(state.1, node);
    if tag == NODE_EXPR && expr_ty_of(state.1, node) == NONE {
        expr_set_ty(state.1, node, key);
    } else if tag == NODE_PAT && pat_ty_of(state.1, node) == NONE {
        pat_set_ty(state.1, node, key);
    }
    key
}

fn canon_ty(state: &mut State, ty: i64, self_key: i64, write: i64) -> i64 {
    if node_tag(state.1, ty) != NODE_TY {
        return unknown_key(state.1, state.2);
    }
    let kind = node_a(state.1, ty);
    let key = canon_ty_kind(state, ty, kind, self_key, write);
    if write == 1 {
        ty_set_key(state.1, ty, key);
    }
    key
}

fn canon_ty_kind(state: &mut State, ty: i64, kind: i64, self_key: i64, write: i64) -> i64 {
    let file = node_file(state.1, ty);
    let start = node_start(state.1, ty);
    let end = node_end(state.1, ty);
    if kind == TY_NAMED {
        let name = node_b(state.1, ty);
        let found = lookup(state.4, name);
        if found.0 != NONE {
            return found.0;
        }
        let sym = ty_sym_of(state.1, ty);
        if sym == NONE {
            push_error(state.3, &format!("unknown type '{}'", name_text(state.0, name)), file, start, end);
            return unknown_key(state.1, state.2);
        }
        return named_key(state.0, state.1, state.2, state.3, sym, (file, start, end));
    }
    if kind == TY_PATH {
        let sym = ty_sym_of(state.1, ty);
        if sym == NONE {
            push_error(state.3, "cannot resolve type", file, start, end);
            return unknown_key(state.1, state.2);
        }
        return named_key(state.0, state.1, state.2, state.3, sym, (file, start, end));
    }
    if kind == TY_GENERIC {
        let sym = ty_sym_of(state.1, ty);
        if sym == NONE {
            push_error(state.3, "cannot resolve type", file, start, end);
            return unknown_key(state.1, state.2);
        }
        if sym_kind(state.1, sym) == SYM_TYPE && sym_decl(state.1, sym) == NONE {
            push_error(state.3, &format!("builtin type '{}' does not take type arguments", name_text(state.0, sym_name(state.1, sym))), file, start, end);
            return unknown_key(state.1, state.2);
        }
        let targs = node_c(state.1, ty);
        let args = canon_ty_list(state, targs, self_key, write);
        let kind_of = if sym_kind(state.1, sym) == SYM_STRUCT { TYD_STRUCT } else if sym_kind(state.1, sym) == SYM_ENUM { TYD_ENUM } else { TYD_NATIVE };
        return canon_tyinfo(state.1, state.2, kind_of, sym, args, NONE, NONE);
    }
    if kind == TY_REF || kind == TY_REF_MUT {
        let inner_ty = node_b(state.1, ty);
        let inner = canon_ty(state, inner_ty, self_key, write);
        let kind_of = if kind == TY_REF { TYD_REF } else { TYD_REF_MUT };
        return canon_tyinfo(state.1, state.2, kind_of, NONE, NONE, inner, NONE);
    }
    if kind == TY_SLICE {
        let elem_ty = node_b(state.1, ty);
        let elem = canon_ty(state, elem_ty, self_key, write);
        return canon_tyinfo(state.1, state.2, TYD_SLICE, NONE, NONE, elem, NONE);
    }
    if kind == TY_ARRAY {
        let elem_ty = node_b(state.1, ty);
        let elem = canon_ty(state, elem_ty, self_key, write);
        return canon_tyinfo(state.1, state.2, TYD_ARRAY, NONE, NONE, elem, node_c(state.1, ty));
    }
    if kind == TY_SELF {
        return self_key;
    }
    if kind == TY_PARAM {
        let name = node_b(state.1, ty);
        let found = lookup(state.4, name);
        if found.0 != NONE {
            return found.0;
        }
        push_error(state.3, &format!("unknown type parameter '{}'", name_text(state.0, name)), file, start, end);
        return unknown_key(state.1, state.2);
    }
    push_error(state.3, "malformed type", file, start, end);
    unknown_key(state.1, state.2)
}

fn canon_ty_list(state: &mut State, list: i64, self_key: i64, write: i64) -> i64 {
    let fresh = alloc_list(state.2);
    let count = list_len(state.2, list);
    let mut idx = 0i64;
    while idx < count {
        let item = list_get(state.2, list, idx);
        let k = canon_ty(state, item, self_key, write);
        list_push(state.2, fresh, k);
        idx += 1;
    }
    fresh
}

fn fresh_var_local(vars: &mut Vec<(i64, i64)>) -> i64 {
    let var = -(vars.len() as i64) - 2;
    vars.push((var, var));
    var
}

fn key_kind(nodes: &[i64], key: i64) -> i64 {
    if is_var(key) {
        return TYD_UNKNOWN;
    }
    let row = find_tyinfo(nodes, key);
    if row == NONE {
        TYD_UNKNOWN
    } else {
        node_b(nodes, row)
    }
}

fn key_sym(nodes: &[i64], key: i64) -> i64 {
    let row = find_tyinfo(nodes, key);
    if row == NONE {
        NONE
    } else {
        node_c(nodes, row)
    }
}

fn key_args(nodes: &[i64], key: i64) -> i64 {
    let row = find_tyinfo(nodes, key);
    if row == NONE {
        NONE
    } else {
        node_d(nodes, row)
    }
}

fn key_elem(nodes: &[i64], key: i64) -> i64 {
    let row = find_tyinfo(nodes, key);
    if row == NONE {
        NONE
    } else {
        node_e(nodes, row)
    }
}

fn key_len(nodes: &[i64], key: i64) -> i64 {
    let row = find_tyinfo(nodes, key);
    if row == NONE {
        NONE
    } else {
        node_f(nodes, row)
    }
}

fn is_int_key(nodes: &[i64], key: i64) -> bool {
    key_kind(nodes, key) == TYD_BUILTIN && builtin_int_is_int(tyinfo_builtin_kind(nodes, key))
}

// True when the builtin key is a signed integer (I8..Isize).
fn key_is_signed(nodes: &[i64], key: i64) -> bool {
    key_kind(nodes, key) == TYD_BUILTIN && builtin_int_is_signed(tyinfo_builtin_kind(nodes, key))
}

fn is_bool_key(nodes: &[i64], key: i64) -> bool {
    key_kind(nodes, key) == TYD_BUILTIN && tyinfo_builtin_kind(nodes, key) == BUILTIN_BOOL
}

// True when a comparison operator is defined on operands of this type.
//
// Comparison is a scalar operation: `==` and `!=` compare integers and
// `Bool`, and the ordering operators compare integers, since ordering
// `Bool` names nothing. There is no structural equality in the language
// and no operator overloading, so a struct, enum, array, slice, reference,
// or native handle has no comparison to lower — aggregates are taken apart
// with `match` and field access instead. Rejecting these here is what
// keeps codegen from being handed an aggregate where it expects a scalar.
fn comparable_key(nodes: &[i64], key: i64, op: i64) -> bool {
    if is_int_key(nodes, key) {
        return true;
    }
    is_bool_key(nodes, key) && (op == BIN_EQ || op == BIN_NE)
}

fn is_result_key(nodes: &[i64], key: i64) -> bool {
    key_kind(nodes, key) == TYD_ENUM && sym_prim_kind(nodes, key_sym(nodes, key)) == PRIM_RESULT
}

fn is_option_key(nodes: &[i64], key: i64) -> bool {
    key_kind(nodes, key) == TYD_ENUM && sym_prim_kind(nodes, key_sym(nodes, key)) == PRIM_OPTION
}

fn attach_variant_facts(nodes: &mut Vec<i64>, lists: &[Vec<i64>]) {
    let mut idx = 0i64;
    while idx < nodes.len() as i64 / NODE_STRIDE {
        if node_tag(nodes, idx) == NODE_TYINFO && node_b(nodes, idx) == TYD_ENUM {
            let key = node_a(nodes, idx);
            let sym = node_c(nodes, idx);
            if sym != NONE {
                let decl = sym_decl(nodes, sym);
                if decl != NONE && node_tag(nodes, decl) == NODE_ITEM && node_a(nodes, decl) == ITEM_ENUM {
                    let variants = node_e(nodes, decl);
                    let count = list_len(lists, variants);
                    let mut v = 0i64;
                    while v < count {
                        let variant = list_get(lists, variants, v);
                        let vsym = variant_sym_of(nodes, variant);
                        if vsym != NONE {
                            alloc_varfact(nodes, key, node_a(nodes, variant), vsym, v);
                        }
                        v += 1;
                    }
                }
            }
        }
        idx += 1;
    }
}

fn attach_linearity(nodes: &mut Vec<i64>, lists: &mut Vec<Vec<i64>>) {
    let mut seen: Vec<i64> = Vec::new();
    let mut idx = 0i64;
    while idx < nodes.len() as i64 / NODE_STRIDE {
        if node_tag(nodes, idx) == NODE_TYINFO {
            seen.clear();
            linear_of(nodes, lists, node_a(nodes, idx), &mut seen);
            // A native container holds linear elements when any of its type
            // arguments is linear (HashMap(K, V): the key counts too).  The
            // flag is attached per canonical key so the borrow checker reads
            // one integer instead of re-deriving linearity (Single-Fact).
            if node_b(nodes, idx) == TYD_NATIVE {
                let args = node_d(nodes, idx);
                let count = list_len(lists, args);
                let mut has = 0;
                let mut ai = 0i64;
                while ai < count {
                    if linear_of(nodes, lists, list_get(lists, args, ai), &mut seen) == 1 {
                        has = 1;
                    }
                    ai += 1;
                }
                node_set(nodes, idx, NODE_START, has);
            }
        }
        idx += 1;
    }
}

fn has_value(list: &[i64], value: i64) -> bool {
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

fn linear_of(nodes: &mut Vec<i64>, lists: &mut Vec<Vec<i64>>, key: i64, seen: &mut Vec<i64>) -> i64 {
    if key < 0 {
        return 0;
    }
    let row = find_tyinfo(nodes, key);
    if row == NONE {
        return 0;
    }
    let stored = node_get(nodes, row, NODE_FILE);
    if stored == 0 || stored == 1 {
        return stored;
    }
    if has_value(seen, key) {
        return 0;
    }
    seen.push(key);
    let kind = node_b(nodes, row);
    let flag = if kind == TYD_NATIVE {
        1
    } else if kind == TYD_ARRAY {
        linear_of(nodes, lists, node_e(nodes, row), seen)
    } else if kind == TYD_STRUCT || kind == TYD_ENUM {
        linear_members_of(nodes, lists, node_c(nodes, row), key, seen)
    } else if kind == TYD_PARAM {
        // Type parameters carry no linearity bound in the grammar, so the
        // only sound default is to treat them as linear (MANIFESTO): a
        // generic body must consume its type-parameter values exactly once.
        1
    } else {
        0
    };
    node_set(nodes, row, NODE_FILE, flag);
    flag
}

fn linear_members_of(nodes: &mut Vec<i64>, lists: &mut Vec<Vec<i64>>, sym: i64, key: i64, seen: &mut Vec<i64>) -> i64 {
    if sym == NONE {
        return 0;
    }
    let decl = sym_decl(nodes, sym);
    if decl == NONE || node_tag(nodes, decl) != NODE_ITEM {
        return 0;
    }
    let kind = node_a(nodes, decl);
    let row = find_tyinfo(nodes, key);
    let args = if row == NONE { NONE } else { node_d(nodes, row) };
    if kind == ITEM_STRUCT {
        let fields = node_e(nodes, decl);
        let count = list_len(lists, fields);
        let mut idx = 0i64;
        while idx < count {
            let fty_node = node_b(nodes, list_get(lists, fields, idx));
            let fty = subst_declared_key(nodes, lists, decl, args, ty_key_of(nodes, fty_node));
            if linear_of(nodes, lists, fty, seen) == 1 {
                return 1;
            }
            idx += 1;
        }
    } else if kind == ITEM_ENUM {
        let variants = node_e(nodes, decl);
        let count = list_len(lists, variants);
        let mut idx = 0i64;
        while idx < count {
            let payload = node_b(nodes, list_get(lists, variants, idx));
            let pcount = list_len(lists, payload);
            let mut pidx = 0i64;
            while pidx < pcount {
                let pty_node = list_get(lists, payload, pidx);
                let pty = subst_declared_key(nodes, lists, decl, args, ty_key_of(nodes, pty_node));
                if linear_of(nodes, lists, pty, seen) == 1 {
                    return 1;
                }
                pidx += 1;
            }
            idx += 1;
        }
    }
    0
}

// Whether a canonical type key's value can carry a reference anywhere in its
// structure, not only when the key itself is bare `&T`/`&mut T`/`&[T]`. The
// borrow checker's returned-borrow obligation (Manifesto principle 5) must
// apply to a function returning `Result(&T, E)` or a struct with a reference
// field the same way it applies to a bare `&T` return; gating on the key's
// own bare kind let a dangling reference escape wrapped in either shape.
// Mirrors `linear_of`'s struct/enum-member walk (identical substitution,
// identical cycle guard) because it is the same question -- "does every
// concrete instantiation of this type carry X" -- for a different X, so a
// second, independent member-walk is not worth introducing for it. Callers
// pass a fresh `seen` per top-level query; unlike `linear_of` this is not
// memoized onto the tyinfo row (no spare payload slot for a second flag),
// which is a bounded cost paid at case-fold, not at every use.
pub fn type_contains_ref(nodes: &mut Vec<i64>, lists: &mut Vec<Vec<i64>>, key: i64, seen: &mut Vec<i64>) -> bool {
    if key < 0 {
        return false;
    }
    let row = find_tyinfo(nodes, key);
    if row == NONE {
        return false;
    }
    if has_value(seen, key) {
        return false;
    }
    seen.push(key);
    let kind = node_b(nodes, row);
    if kind == TYD_REF || kind == TYD_REF_MUT || kind == TYD_SLICE {
        return true;
    }
    if kind == TYD_ARRAY {
        return type_contains_ref(nodes, lists, node_e(nodes, row), seen);
    }
    if kind == TYD_STRUCT || kind == TYD_ENUM {
        return ref_members_of(nodes, lists, node_c(nodes, row), key, seen);
    }
    false
}

fn ref_members_of(nodes: &mut Vec<i64>, lists: &mut Vec<Vec<i64>>, sym: i64, key: i64, seen: &mut Vec<i64>) -> bool {
    if sym == NONE {
        return false;
    }
    let decl = sym_decl(nodes, sym);
    if decl == NONE || node_tag(nodes, decl) != NODE_ITEM {
        return false;
    }
    let kind = node_a(nodes, decl);
    let row = find_tyinfo(nodes, key);
    let args = if row == NONE { NONE } else { node_d(nodes, row) };
    if kind == ITEM_STRUCT {
        let fields = node_e(nodes, decl);
        let count = list_len(lists, fields);
        let mut idx = 0i64;
        while idx < count {
            let fty_node = node_b(nodes, list_get(lists, fields, idx));
            let fty = subst_declared_key(nodes, lists, decl, args, ty_key_of(nodes, fty_node));
            if type_contains_ref(nodes, lists, fty, seen) {
                return true;
            }
            idx += 1;
        }
    } else if kind == ITEM_ENUM {
        let variants = node_e(nodes, decl);
        let count = list_len(lists, variants);
        let mut idx = 0i64;
        while idx < count {
            let payload = node_b(nodes, list_get(lists, variants, idx));
            let pcount = list_len(lists, payload);
            let mut pidx = 0i64;
            while pidx < pcount {
                let pty_node = list_get(lists, payload, pidx);
                let pty = subst_declared_key(nodes, lists, decl, args, ty_key_of(nodes, pty_node));
                if type_contains_ref(nodes, lists, pty, seen) {
                    return true;
                }
                pidx += 1;
            }
            idx += 1;
        }
    }
    false
}

fn subst_declared_key(
    nodes: &mut Vec<i64>,
    lists: &mut Vec<Vec<i64>>,
    decl: i64,
    args: i64,
    declared: i64,
) -> i64 {
    if declared == NONE {
        return declared;
    }
    let params = node_f(nodes, decl);
    let pcount = list_len(lists, params);
    let acount = list_len(lists, args);
    if pcount == 0 || pcount != acount {
        return declared;
    }
    let mut from: Vec<i64> = Vec::new();
    let mut to: Vec<i64> = Vec::new();
    let mut idx = 0i64;
    while idx < pcount {
        let param = list_get(lists, params, idx);
        if node_tag(nodes, param) == NODE_TY && node_a(nodes, param) == TY_PARAM {
            from.push(ty_key_of(nodes, param));
            to.push(list_get(lists, args, idx));
        }
        idx += 1;
    }
    if from.is_empty() {
        return declared;
    }
    subst_key(nodes, lists, declared, &from, &to)
}

// One fact row per (canonical struct key, field name): the substituted
// field key and its declared-order index, computed here from the declared
// field types and the key's own type arguments.  The borrow checker and
// codegen read these rows instead of re-walking ITEM_STRUCT lists and
// re-running generic substitution (Single-Fact Rule).
fn attach_fieldkey_facts(nodes: &mut Vec<i64>, lists: &mut Vec<Vec<i64>>) {
    let mut idx = 0i64;
    while idx < nodes.len() as i64 / NODE_STRIDE {
        if node_tag(nodes, idx) == NODE_TYINFO && node_b(nodes, idx) == TYD_STRUCT {
            let key = node_a(nodes, idx);
            let sym = node_c(nodes, idx);
            if sym != NONE {
                let decl = sym_decl(nodes, sym);
                if decl != NONE && node_tag(nodes, decl) == NODE_ITEM && node_a(nodes, decl) == ITEM_STRUCT {
                    let fields = node_e(nodes, decl);
                    let count = list_len(lists, fields);
                    let from = declared_param_keys(nodes, lists, decl);
                    let to = list_to_vec(lists, key_args(nodes, key));
                    let mut f = 0i64;
                    while f < count {
                        let field = list_get(lists, fields, f);
                        let declared = ty_key_of(nodes, node_b(nodes, field));
                        let fkey = subst_key(nodes, lists, declared, &from, &to);
                        alloc_fieldkey(nodes, key, node_a(nodes, field), fkey, f);
                        f += 1;
                    }
                }
            }
        }
        idx += 1;
    }
}

fn attach_type_facts(nodes: &mut Vec<i64>, lists: &mut Vec<Vec<i64>>) {
    attach_variant_facts(nodes, lists);
    attach_fieldkey_facts(nodes, lists);
    attach_linearity(nodes, lists);
}

fn unify_key(nodes: &[i64], lists: &[Vec<i64>], vars: &mut Vec<(i64, i64)>, a: i64, b: i64) -> bool {
    let ra = resolve_var(vars, a);
    let rb = resolve_var(vars, b);
    if ra == rb {
        return true;
    }
    if is_var(ra) {
        bind_var(vars, ra, rb);
        return true;
    }
    if is_var(rb) {
        bind_var(vars, rb, ra);
        return true;
    }
    let row_a = find_tyinfo(nodes, ra);
    let row_b = find_tyinfo(nodes, rb);
    if row_a == NONE || row_b == NONE {
        return false;
    }
    if node_b(nodes, row_a) != node_b(nodes, row_b) {
        return false;
    }
    let kind = node_b(nodes, row_a);
    if kind == TYD_PARAM {
        return false;
    }
    if node_c(nodes, row_a) != node_c(nodes, row_b) {
        return false;
    }
    if node_f(nodes, row_a) != node_f(nodes, row_b) {
        return false;
    }
    let args_a = node_d(nodes, row_a);
    let args_b = node_d(nodes, row_b);
    let na = list_len(lists, args_a);
    let nb = list_len(lists, args_b);
    if na != nb {
        return false;
    }
    let mut idx = 0i64;
    while idx < na {
        if !unify_key(nodes, lists, vars, list_get(lists, args_a, idx), list_get(lists, args_b, idx)) {
            return false;
        }
        idx += 1;
    }
    let elem_a = node_e(nodes, row_a);
    let elem_b = node_e(nodes, row_b);
    if (elem_a != NONE || elem_b != NONE)
        && !unify_key(nodes, lists, vars, elem_a, elem_b) {
            return false;
        }
    true
}

fn render_key(
    names: &[String],
    nodes: &[i64],
    lists: &[Vec<i64>],
    vars: &[(i64, i64)],
    origins: &[(i64, i64, i64)],
    key: i64,
) -> String {
    if is_var(key) {
        let resolved = resolve_var(vars, key);
        if !is_var(resolved) {
            return render_key(names, nodes, lists, vars, origins, resolved);
        }
        let name = var_origin_name(origins, key);
        if name != NONE {
            return format!("type parameter '{}'", name_text(names, name));
        }
        return "?".to_string();
    }
    let row = find_tyinfo(nodes, key);
    if row == NONE {
        return "?".to_string();
    }
    let kind = node_b(nodes, row);
    if kind == TYD_UNKNOWN {
        return "?".to_string();
    }
    if kind == TYD_PARAM {
        return name_text(names, node_c(nodes, row));
    }
    let sym = node_c(nodes, row);
    let elem = node_e(nodes, row);
    let args = node_d(nodes, row);
    if kind == TYD_REF {
        return format!("&{}", render_key(names, nodes, lists, vars, origins, elem));
    }
    if kind == TYD_REF_MUT {
        return format!("&mut {}", render_key(names, nodes, lists, vars, origins, elem));
    }
    if kind == TYD_SLICE {
        return format!("[{}]", render_key(names, nodes, lists, vars, origins, elem));
    }
    if kind == TYD_ARRAY {
        return format!("[{}; {}]", render_key(names, nodes, lists, vars, origins, elem), node_f(nodes, row));
    }
    let mut text = name_text(names, sym_name(nodes, sym));
    let count = list_len(lists, args);
    if count > 0 {
        let mut parts: Vec<String> = Vec::new();
        let mut idx = 0i64;
        while idx < count {
            parts.push(render_key(names, nodes, lists, vars, origins, list_get(lists, args, idx)));
            idx += 1;
        }
        text = format!("{}({})", text, parts.join(", "));
    }
    text
}

/// Render a canonical type key for display outside the typechecker (the
/// arena dump, layout printing, and the language server).  Attached keys are
/// fully resolved after type checking, so no inference-variable bindings or
/// origin table are needed; this is the same rendering the typechecker's own
/// diagnostics use.
pub fn render_type_key(names: &[String], nodes: &[i64], lists: &[Vec<i64>], key: i64) -> String {
    render_key(names, nodes, lists, &[], &[], key)
}

fn var_origin_name(origins: &[(i64, i64, i64)], var: i64) -> i64 {
    let mut idx = 0usize;
    while idx < origins.len() {
        match origins.get(idx) {
            Some(entry) => {
                if entry.0 == var {
                    return entry.2;
                }
            }
            None => break,
        }
        idx += 1;
    }
    NONE
}

fn key_has_unbound_var(nodes: &[i64], lists: &[Vec<i64>], vars: &[(i64, i64)], key: i64) -> bool {
    if is_var(key) {
        return is_var(resolve_var(vars, key));
    }
    let row = find_tyinfo(nodes, key);
    if row == NONE {
        return false;
    }
    let args = node_d(nodes, row);
    let count = list_len(lists, args);
    let mut idx = 0i64;
    while idx < count {
        if key_has_unbound_var(nodes, lists, vars, list_get(lists, args, idx)) {
            return true;
        }
        idx += 1;
    }
    let elem = node_e(nodes, row);
    if elem != NONE && key_has_unbound_var(nodes, lists, vars, elem) {
        return true;
    }
    false
}

fn collect_types(state: &mut State, list: i64) {
    let count = list_len(state.2, list);
    let mut idx = 0i64;
    while idx < count {
        collect_type_item(state, list_get(state.2, list, idx));
        idx += 1;
    }
}

fn collect_type_item(state: &mut State, item: i64) {
    if node_tag(state.1, item) != NODE_ITEM {
        return;
    }
    let kind = node_a(state.1, item);
    if kind == ITEM_MODULE {
        collect_types(state, node_e(state.1, item));
    } else if kind == ITEM_STRUCT {
        push_scope(state.4);
        bind_type_params(state.1, state.2, state.4, item, node_f(state.1, item));
        let fields = node_e(state.1, item);
        let count = list_len(state.2, fields);
        let mut idx = 0i64;
        while idx < count {
            let fty = node_b(state.1, list_get(state.2, fields, idx));
            canon_ty(state, fty, NONE, 1);
            idx += 1;
        }
        pop_scope(state.4);
    } else if kind == ITEM_ENUM {
        push_scope(state.4);
        bind_type_params(state.1, state.2, state.4, item, node_f(state.1, item));
        let variants = node_e(state.1, item);
        let count = list_len(state.2, variants);
        let mut idx = 0i64;
        while idx < count {
            let vty = node_b(state.1, list_get(state.2, variants, idx));
            canon_ty_list(state, vty, NONE, 1);
            idx += 1;
        }
        pop_scope(state.4);
    } else if kind == ITEM_NATIVE_TYPE {
        push_scope(state.4);
        bind_type_params(state.1, state.2, state.4, item, node_e(state.1, item));
        pop_scope(state.4);
    }
}

fn collect_impls(state: &mut State, list: i64) {
    let count = list_len(state.2, list);
    let mut idx = 0i64;
    while idx < count {
        collect_impl_item(state, list_get(state.2, list, idx));
        idx += 1;
    }
}

fn collect_impl_item(state: &mut State, item: i64) {
    if node_tag(state.1, item) != NODE_ITEM {
        return;
    }
    let kind = node_a(state.1, item);
    if kind == ITEM_MODULE {
        let saved_scope = state.13;
        state.13 = module_scope_of(state.1, item);
        collect_impls(state, node_e(state.1, item));
        state.13 = saved_scope;
        return;
    }
    if kind != ITEM_IMPL {
        return;
    }
    let trait_sym = item_sym_of(state.1, item);
    if trait_sym == NONE {
        return;
    }
    let for_ty = node_e(state.1, item);
    let for_key = canon_ty(state, for_ty, NONE, 1);
    // At most one impl of a given trait may exist for a given type; two
    // impls would let impl_find and codegen's deferred dispatch disagree.
    let mut di = 0i64;
    while di < state.5.len() as i64 / IMPL_STRIDE {
        if impl_at(state.5, (di * IMPL_STRIDE) as usize) == trait_sym
            && impl_at(state.5, (di * IMPL_STRIDE + 1) as usize) == for_key
        {
            push_error(state.3, &format!("duplicate impl of trait '{}' for type '{}'", name_text(state.0, sym_name(state.1, trait_sym)), render_key(state.0, state.1, state.2, state.6, state.7, for_key)), node_file(state.1, item), node_start(state.1, item), node_end(state.1, item));
            return;
        }
        di += 1;
    }
    let methods = node_f(state.1, item);
    let method_count = list_len(state.2, methods);
    let mut idx = 0i64;
    while idx < method_count {
        let method = list_get(state.2, methods, idx);
        check_fn(state, method, for_key, 0);
        verify_impl_method(state, trait_sym, for_key, method);
        idx += 1;
    }
    verify_impl_complete(state, trait_sym, for_key, item, methods);
    state.5.push(trait_sym);
    state.5.push(for_key);
    state.5.push(methods);
}

/// Reports every method the trait declares that this `impl` does not
/// provide.
///
/// `verify_impl_method` checks the methods an impl *has* against the trait;
/// nothing checked the ones it lacks, so a missing method surfaced only if
/// some call site happened to dispatch it ("impl method not found"), and an
/// incomplete impl that nothing fully exercised compiled cleanly. A trait
/// method is a signature with no body — the parser gives trait methods no
/// body at all, so the language has no default/provided methods for one to
/// fall back on — which makes every declared method mandatory and this a
/// plain set difference.
fn verify_impl_complete(state: &mut State, trait_sym: i64, for_key: i64, item: i64, methods: i64) {
    let trait_item = sym_decl(state.1, trait_sym);
    if trait_item == NONE {
        return;
    }
    let declared = node_e(state.1, trait_item);
    let count = list_len(state.2, declared);
    let file = node_file(state.1, item);
    let start = node_start(state.1, item);
    let end = node_end(state.1, item);
    let mut idx = 0i64;
    while idx < count {
        let trait_method = list_get(state.2, declared, idx);
        let name = node_a(state.1, trait_method);
        if find_method_by_name(state.1, state.2, methods, name) == NONE {
            push_error(
                state.3,
                &format!(
                    "impl of trait '{}' for '{}' is missing method '{}'",
                    name_text(state.0, sym_name(state.1, trait_sym)),
                    render_key(state.0, state.1, state.2, state.6, state.7, for_key),
                    name_text(state.0, name)
                ),
                file,
                start,
                end,
            );
        }
        idx += 1;
    }
}

fn verify_impl_method(state: &mut State, trait_sym: i64, for_key: i64, method: i64) {
    let trait_item = sym_decl(state.1, trait_sym);
    if trait_item == NONE {
        return;
    }
    let trait_method = find_method_by_name(state.1, state.2, node_e(state.1, trait_item), node_a(state.1, method));
    if trait_method == NONE {
        let file = node_file(state.1, method);
        let start = node_start(state.1, method);
        let end = node_end(state.1, method);
        push_error(state.3, &format!("impl method '{}' does not match any trait method", name_text(state.0, node_a(state.1, method))), file, start, end);
        return;
    }
    push_scope(state.4);
    let mut t_vars: Vec<(i64, i64)> = Vec::new();
    let t_params = node_b(state.1, trait_method);
    let t_count = list_len(state.2, t_params);
    let mut pidx = 0i64;
    while pidx < t_count {
        let t_param = list_get(state.2, t_params, pidx);
        if node_tag(state.1, t_param) == NODE_TY && node_a(state.1, t_param) == TY_PARAM {
            bind(state.4, node_b(state.1, t_param), fresh_var_local(&mut t_vars), 0, NONE);
        }
        pidx += 1;
    }
    let self_var = fresh_var_local(&mut t_vars);
    bind(state.4, intern(state.0, "Self"), self_var, 0, NONE);
    let t_params = node_c(state.1, trait_method);
    let i_params = node_c(state.1, method);
    let tn = list_len(state.2, t_params);
    let in_count = list_len(state.2, i_params);
    let mut ok = tn == in_count;
    let mut idx = 0i64;
    while idx < tn {
        let t_param = list_get(state.2, t_params, idx);
        let t_ty = node_b(state.1, t_param);
        let t_key = canon_ty(state, t_ty, self_var, 0);
        let i_param = list_get(state.2, i_params, idx);
        let i_ty = node_b(state.1, i_param);
        let i_key = canon_ty(state, i_ty, for_key, 0);
        let unify_ok = unify_key(state.1, state.2, &mut t_vars, t_key, i_key);
        if !unify_ok {
            ok = false;
        }
        idx += 1;
    }
    let t_ret_ty = node_d(state.1, trait_method);
    let t_ret = canon_ty(state, t_ret_ty, self_var, 0);
    let i_ret_ty = node_d(state.1, method);
    let i_ret = canon_ty(state, i_ret_ty, for_key, 0);
    let ret_ok = unify_key(state.1, state.2, &mut t_vars, t_ret, i_ret);
    if !ret_ok {
        ok = false;
    }
    if in_count != tn {
        ok = false;
    }
    if !ok {
        let file = node_file(state.1, method);
        let start = node_start(state.1, method);
        let end = node_end(state.1, method);
        push_error(state.3, &format!("impl method '{}' signature does not match the trait declaration", name_text(state.0, node_a(state.1, method))), file, start, end);
    }
    pop_scope(state.4);
}

fn find_method_by_name(nodes: &[i64], lists: &[Vec<i64>], methods: i64, name: i64) -> i64 {
    let count = list_len(lists, methods);
    let mut idx = 0i64;
    while idx < count {
        let method = list_get(lists, methods, idx);
        if node_a(nodes, method) == name {
            return method;
        }
        idx += 1;
    }
    NONE
}

fn impl_find(impls: &[i64], trait_sym: i64, for_key: i64) -> i64 {
    let mut idx = 0i64;
    while idx < impls.len() as i64 / IMPL_STRIDE {
        if impl_at(impls, (idx * IMPL_STRIDE) as usize) == trait_sym
            && impl_at(impls, (idx * IMPL_STRIDE + 1) as usize) == for_key
        {
            return idx;
        }
        idx += 1;
    }
    NONE
}

fn impl_methods(impls: &[i64], idx: i64) -> i64 {
    impl_at(impls, (idx * IMPL_STRIDE + 2) as usize)
}

fn is_unit_key(nodes: &[i64], key: i64) -> bool {
    key_kind(nodes, key) == TYD_ENUM && sym_prim_kind(nodes, key_sym(nodes, key)) == PRIM_UNIT
}

fn unit_key_of(state: &mut State) -> i64 {
    let sym = state.8;
    if sym == NONE {
        unknown_key(state.1, state.2)
    } else {
        canon_tyinfo(state.1, state.2, TYD_ENUM, sym, NONE, NONE, NONE)
    }
}

fn check_fn_list(state: &mut State, list: i64) {
    let count = list_len(state.2, list);
    let mut idx = 0i64;
    while idx < count {
        check_fn_item(state, list_get(state.2, list, idx));
        idx += 1;
    }
}

fn check_fn_item(state: &mut State, item: i64) {
    if node_tag(state.1, item) != NODE_ITEM {
        return;
    }
    let kind = node_a(state.1, item);
    if kind == ITEM_MODULE {
        let saved_scope = state.13;
        state.13 = module_scope_of(state.1, item);
        check_fn_list(state, node_e(state.1, item));
        state.13 = saved_scope;
    } else if kind == ITEM_FUN || kind == ITEM_NATIVE_FUN {
        let sym = item_sym_of(state.1, item);
        let is_main = if sym != NONE && node_f(state.1, sym) == SYM_FUN_MAIN { 1 } else { 0 };
        check_fn(state, node_d(state.1, item), NONE, is_main);
    }
}

// The resolver stores every module's scope id on its symbol (slot e); the
// typechecker tracks the scope it is currently walking so field accesses can
// be checked against the declaring module.  The root item list is scope 0.
fn module_scope_of(nodes: &[i64], item: i64) -> i64 {
    let sym = item_sym_of(nodes, item);
    if sym == NONE {
        0
    } else {
        node_e(nodes, sym)
    }
}

fn check_fn_sigs_list(state: &mut State, list: i64) {
    let count = list_len(state.2, list);
    let mut idx = 0i64;
    while idx < count {
        check_fn_sigs_item(state, list_get(state.2, list, idx));
        idx += 1;
    }
}

fn check_fn_sigs_item(state: &mut State, item: i64) {
    if node_tag(state.1, item) != NODE_ITEM {
        return;
    }
    let kind = node_a(state.1, item);
    if kind == ITEM_MODULE {
        check_fn_sigs_list(state, node_e(state.1, item));
    } else if kind == ITEM_FUN || kind == ITEM_NATIVE_FUN {
        check_fn_sigs(state, node_d(state.1, item));
    } else if kind == ITEM_TRAIT {
        // Trait method signatures are canon'd here (with write) so the
        // borrow checker reads their parameter and return keys from the
        // attached type rows instead of re-deriving modes from raw
        // NODE_TY tags (Single-Fact Rule).  The methods have no bodies, so
        // only their signatures are visited.
        let methods = node_e(state.1, item);
        let count = list_len(state.2, methods);
        let mut idx = 0i64;
        while idx < count {
            check_fn_sigs(state, list_get(state.2, methods, idx));
            idx += 1;
        }
    }
}

fn check_fn_sigs(state: &mut State, fn_node: i64) {
    if node_tag(state.1, fn_node) != NODE_FN {
        return;
    }
    push_scope(state.4);
    bind_type_params(state.1, state.2, state.4, fn_node, node_b(state.1, fn_node));
    let params = node_c(state.1, fn_node);
    let count = list_len(state.2, params);
    let mut idx = 0i64;
    while idx < count {
        let param = list_get(state.2, params, idx);
        canon_ty(state, node_b(state.1, param), NONE, 1);
        idx += 1;
    }
    canon_ty(state, node_d(state.1, fn_node), NONE, 1);
    pop_scope(state.4);
}

fn check_fn(state: &mut State, fn_node: i64, self_key: i64, is_main: i64) {
    if node_tag(state.1, fn_node) != NODE_FN {
        return;
    }
    push_scope(state.4);
    bind_type_params(state.1, state.2, state.4, fn_node, node_b(state.1, fn_node));
    let params = node_c(state.1, fn_node);
    let count = list_len(state.2, params);
    let mut idx = 0i64;
    while idx < count {
        let param = list_get(state.2, params, idx);
        let param_ty = node_b(state.1, param);
        let key = canon_ty(state, param_ty, self_key, 1);
        bind(state.4, node_a(state.1, param), key, 0, param);
        idx += 1;
    }
    let ret_ty = node_d(state.1, fn_node);
    let ret = canon_ty(state, ret_ty, self_key, 1);
    let saved_ret_ty_node = state.17;
    state.17 = ret_ty;
    // The program entry point (`SYM_FUN_MAIN`, set by the resolver) must
    // return a builtin scalar, Unit, or an exit-status enum (MANIFESTO):
    // codegen derives the process exit code only from those two layouts.
    if is_main == 1 {
        let ret_kind = key_kind(state.1, ret);
        if ret_kind != TYD_BUILTIN && ret_kind != TYD_ENUM {
            push_error(state.3, "main must return a builtin scalar, Unit, or an exit-status enum", node_file(state.1, ret_ty), node_start(state.1, ret_ty), node_end(state.1, ret_ty));
        } else if ret_kind == TYD_ENUM {
            // Unit is the only non-exit-status enum `main` may return.
            let esym = key_sym(state.1, ret);
            if esym != NONE && sym_prim_kind(state.1, esym) != PRIM_UNIT {
                check_exit_status_enum(state, esym, ret_ty);
            }
        }
    }
    let impure = node_e(state.1, fn_node);
    let body = node_f(state.1, fn_node);
    attach_local_facts(state, fn_node);
    if body != NONE {
        check_stmt_list(state, body, ret, impure, self_key);
    }
    check_tail_calls(state, fn_node);
    pop_scope(state.4);
    state.17 = saved_ret_ty_node;
}

// The exit-status enum contract (MANIFESTO): 2 or 3 variants shaped
// (Success, Failure, Optional Diagnostic(Int)) — the first two carry no
// payload, and the optional third carries exactly one integer-scalar
// payload used as the process exit code.  Any other enum returned from
// `main` is a compile error; codegen derives the exit code only from
// this shape.
fn check_exit_status_enum(state: &mut State, esym: i64, ret_ty: i64) {
    let decl = sym_decl(state.1, esym);
    if decl == NONE || node_tag(state.1, decl) != NODE_ITEM || node_a(state.1, decl) != ITEM_ENUM {
        return;
    }
    let variants = node_e(state.1, decl);
    let vcount = list_len(state.2, variants);
    let mut ok = vcount == 2 || vcount == 3;
    if ok {
        ok = variant_payload_len(state, list_get(state.2, variants, 0)) == 0
            && variant_payload_len(state, list_get(state.2, variants, 1)) == 0;
    }
    if ok && vcount == 3 {
        let diag = list_get(state.2, variants, 2);
        let payload_list = node_b(state.1, diag);
        let payload = list_first(state.2, payload_list);
        let payload_key = if payload != NONE && node_tag(state.1, payload) == NODE_TY {
            ty_key_of(state.1, payload)
        } else {
            NONE
        };
        ok = list_len(state.2, payload_list) == 1 && is_int_key(state.1, payload_key);
    }
    if !ok {
        push_error(
            state.3,
            &format!(
                "main return enum '{}' does not conform to the exit-status enum contract: expected 2 or 3 variants with shape (Success, Failure, Optional Diagnostic(Int))",
                name_text(state.0, node_b(state.1, esym))
            ),
            node_file(state.1, ret_ty),
            node_start(state.1, ret_ty),
            node_end(state.1, ret_ty),
        );
    }
}

// The payload count of a declared variant (slot b is its payload type list).
fn variant_payload_len(state: &mut State, variant: i64) -> i64 {
    if variant == NONE || node_tag(state.1, variant) != NODE_VARIANT {
        -1
    } else {
        list_len(state.2, node_b(state.1, variant))
    }
}

// Sentinel for a tail-unsafe call whose reference cannot be pinned to a
// single frame-local binding to name (a `match`/`try` returning a
// reference).  It is still rejected and still truthfully reported; only the
// variable name is absent.
const TAIL_ROOT_UNNAMED: i64 = -2;

// The frame-local root of a reference argument (MANIFESTO's tail-call law).
// Returns the name id of a binding in the current function's frame that
// `expr`'s reference value is rooted in, `TAIL_ROOT_UNNAMED` when it is
// frame-rooted but no single binding names it, or NONE when the value
// provably does not point into the current frame.  A reference points into
// the frame only when it was (transitively) borrowed from a local or
// by-value parameter of the current function; a reference received as an
// incoming reference parameter, or read from static storage, points outside
// it and is safe to pass through a tail call.
fn expr_frame_root(state: &mut State, expr: i64) -> i64 {
    if node_tag(state.1, expr) != NODE_EXPR {
        return NONE;
    }
    let key = expr_ty_of(state.1, expr);
    if key == NONE {
        return NONE;
    }
    let mut seen: Vec<i64> = Vec::new();
    if !type_contains_ref(state.1, state.2, key, &mut seen) {
        return NONE;
    }
    let kind = node_a(state.1, expr);
    if kind == EXPR_LIT {
        // The only reference-typed literal is a string, which is static.
        return NONE;
    }
    if kind == EXPR_PATH {
        return path_value_root(state, expr);
    }
    if kind == EXPR_UNARY {
        let op = node_b(state.1, expr);
        if op == UN_REF || op == UN_REF_MUT {
            return place_frame_root(state, node_c(state.1, expr));
        }
        return NONE;
    }
    if kind == EXPR_FIELD_ACCESS {
        return expr_frame_root(state, node_b(state.1, expr));
    }
    if kind == EXPR_INDEX {
        return expr_frame_root(state, node_b(state.1, expr));
    }
    if kind == EXPR_CALL {
        // A returned borrow derives from an input reference or static, so
        // the call result is frame-rooted iff one of its own arguments is.
        let args = node_d(state.1, expr);
        let count = list_len(state.2, args);
        let mut idx = 0i64;
        while idx < count {
            let root = expr_frame_root(state, list_get(state.2, args, idx));
            if root != NONE {
                return root;
            }
            idx += 1;
        }
        return NONE;
    }
    if kind == EXPR_STRUCT_LIT {
        let values = node_d(state.1, expr);
        let count = list_len(state.2, values);
        let mut idx = 0i64;
        while idx < count {
            let root = expr_frame_root(state, list_get(state.2, values, idx));
            if root != NONE {
                return root;
            }
            idx += 1;
        }
        return NONE;
    }
    if kind == EXPR_ARRAY {
        let elems = node_b(state.1, expr);
        let count = list_len(state.2, elems);
        let mut idx = 0i64;
        while idx < count {
            let root = expr_frame_root(state, list_get(state.2, elems, idx));
            if root != NONE {
                return root;
            }
            idx += 1;
        }
        return NONE;
    }
    TAIL_ROOT_UNNAMED
}

// The frame root of a `&`/`&mut` operand: the binding whose *storage* the
// borrowed place occupies.  Storage is outside the current frame only when
// it is static or reached through an incoming reference parameter, so a
// bare path (a local, a by-value parameter, or a reference parameter's own
// slot — `&param` is `&&T`, pointing at the parameter's frame slot) is
// frame storage, while a field/index reached through a reference is
// wherever that reference points.
fn place_frame_root(state: &mut State, place: i64) -> i64 {
    if node_tag(state.1, place) != NODE_EXPR {
        return TAIL_ROOT_UNNAMED;
    }
    let kind = node_a(state.1, place);
    if kind == EXPR_PATH {
        let sym = expr_sym_of(state.1, place);
        if sym != NONE {
            return NONE;
        }
        let segs = node_b(state.1, place);
        let first = list_first(state.2, segs);
        let found = lookup_full(state.4, first);
        if found.0 == NONE {
            return TAIL_ROOT_UNNAMED;
        }
        return first;
    }
    if kind == EXPR_FIELD_ACCESS || kind == EXPR_INDEX {
        let base = node_b(state.1, place);
        let base_key = expr_ty_of(state.1, base);
        if base_key != NONE {
            let bk = key_kind(state.1, base_key);
            if bk == TYD_REF || bk == TYD_REF_MUT {
                return expr_frame_root(state, base);
            }
        }
        return place_frame_root(state, base);
    }
    TAIL_ROOT_UNNAMED
}

// The frame root of a reference-typed path value: NONE when the value
// points outside the frame (an incoming reference parameter, or a
// module-level constant/static), the root binding's name otherwise.
fn path_value_root(state: &mut State, expr: i64) -> i64 {
    let sym = expr_sym_of(state.1, expr);
    if sym != NONE {
        return NONE;
    }
    let segs = node_b(state.1, expr);
    let first = list_first(state.2, segs);
    let found = lookup_full(state.4, first);
    if found.0 == NONE {
        return TAIL_ROOT_UNNAMED;
    }
    if found.2 != NONE && node_tag(state.1, found.2) == NODE_PARAM {
        let kind = key_kind(state.1, found.0);
        if kind == TYD_REF || kind == TYD_REF_MUT {
            return NONE;
        }
    }
    // A local binding of reference type points wherever its defining value
    // points: an immutable `val`'s defining value is its initializer, and a
    // match-arm binding's is the scrutinee.  A `var` can be reassigned, so
    // its origin cannot be pinned statically and is conservatively treated
    // as frame-rooted.
    if found.2 != NONE && node_tag(state.1, found.2) == NODE_STMT && node_a(state.1, found.2) == STMT_LET && found.1 == 0 {
        return expr_frame_root(state, node_e(state.1, found.2));
    }
    if found.2 != NONE && node_tag(state.1, found.2) == NODE_PAT {
        let scrutinee = patfact_scrutinee_of(state.1, found.2);
        if scrutinee != NONE {
            return expr_frame_root(state, scrutinee);
        }
    }
    first
}

// Computes and attaches the tail-safety fact for a call (MANIFESTO's
// tail-call law): whether any argument carries a reference into the current
// frame, which would make LLVM's `tail` marker a false promise.  Attached
// during body checking so the scope used to resolve a binding's kind is the
// exact scope the body was checked under; codegen and the self-recursion
// rejection both read the attached fact.
fn attach_call_tail_safe(state: &mut State, expr: i64) {
    let args = node_d(state.1, expr);
    let count = list_len(state.2, args);
    let mut idx = 0i64;
    let mut root = NONE;
    while idx < count {
        let r = expr_frame_root(state, list_get(state.2, args, idx));
        if r != NONE {
            root = r;
        }
        idx += 1;
    }
    let tail_safe = if root == NONE { 1 } else { 0 };
    alloc_callfact(state.1, expr, tail_safe, root);
}

// The O(1) call-stack guarantee (MANIFESTO): every self-recursive call
// must be in strict tail position — the direct expression value of a
// `return`, or the non-diverging result expression of a match in tail
// position — because non-tail self-recursion grows the CPU call stack
// per frame and the runtime guard that once bounded it is retired.  The
// pass runs after the body is checked, so every call carries its
// resolved instance row; tailness is a property of the statement tree,
// so it is computed here by walking it (the resolver attached symbols,
// the typechecker attached instances — nothing is re-derived).
fn check_tail_calls(state: &mut State, fn_node: i64) {
    let body = node_f(state.1, fn_node);
    if body != NONE {
        tail_walk_stmt_list(state, fn_node, body, 0);
    }
}

fn tail_walk_stmt_list(state: &mut State, fn_node: i64, list: i64, tail: i64) {
    let count = list_len(state.2, list);
    let mut idx = 0i64;
    while idx < count {
        tail_walk_stmt(state, fn_node, list_get(state.2, list, idx), tail);
        idx += 1;
    }
}

// `tail` is 1 only for the value expression of a match arm in tail
// position; statement lists (function bodies, loop bodies, if branches)
// never produce tail values, so their expression statements are walked
// with 0 and only their `return`s are tail.
fn tail_walk_stmt(state: &mut State, fn_node: i64, stmt: i64, tail: i64) {
    if node_tag(state.1, stmt) != NODE_STMT {
        return;
    }
    let kind = node_a(state.1, stmt);
    if kind == STMT_RETURN {
        let value = node_b(state.1, stmt);
        if value != NONE {
            tail_walk_expr(state, fn_node, value, 1);
        }
    } else if kind == STMT_LET {
        tail_walk_expr(state, fn_node, node_e(state.1, stmt), 0);
    } else if kind == STMT_ASSIGN {
        tail_walk_expr(state, fn_node, node_b(state.1, stmt), 0);
        tail_walk_expr(state, fn_node, node_c(state.1, stmt), 0);
    } else if kind == STMT_WHILE {
        tail_walk_expr(state, fn_node, node_b(state.1, stmt), 0);
        tail_walk_stmt_list(state, fn_node, node_c(state.1, stmt), 0);
    } else if kind == STMT_IF {
        tail_walk_expr(state, fn_node, node_b(state.1, stmt), 0);
        tail_walk_stmt_list(state, fn_node, node_c(state.1, stmt), 0);
        if node_d(state.1, stmt) != NONE {
            tail_walk_stmt_list(state, fn_node, node_d(state.1, stmt), 0);
        }
    } else if kind == STMT_EXPR {
        tail_walk_expr(state, fn_node, node_b(state.1, stmt), tail);
    }
}

fn tail_walk_expr(state: &mut State, fn_node: i64, expr: i64, tail: i64) {
    if node_tag(state.1, expr) != NODE_EXPR {
        return;
    }
    let kind = node_a(state.1, expr);
    if kind == EXPR_CALL {
        let inst = expr_sym_of(state.1, expr);
        let fn_slot = inst_fn_of(state.1, inst);
        let is_self = node_tag(state.1, fn_slot) == NODE_FN && fn_slot == fn_node;
        if tail == 0 {
            if is_self {
                push_error(
                    state.3,
                    &format!(
                        "non-tail recursive call to '{}' is forbidden: self-recursion must be in tail position (rewrite using an accumulator or an explicit work stack)",
                        name_text(state.0, node_a(state.1, fn_node))
                    ),
                    node_file(state.1, expr),
                    node_start(state.1, expr),
                    node_end(state.1, expr),
                );
            }
        } else if is_self {
            // A self-tail call that passes a borrow of its own frame cannot
            // be a real tail call: reusing the frame would invalidate the
            // borrow (MANIFESTO's O(1) call-stack guarantee).
            let root = callfact_root_name_of(state.1, expr);
            if root != NONE {
                if root >= 0 {
                    push_error(
                        state.3,
                        &format!(
                            "cannot pass borrow of local variable '{}' into tail-recursive call: local does not outlive the frame jump",
                            name_text(state.0, root)
                        ),
                        node_file(state.1, expr),
                        node_start(state.1, expr),
                        node_end(state.1, expr),
                    );
                } else {
                    push_error(
                        state.3,
                        "cannot pass a borrow rooted in this function's frame into tail-recursive call: the borrow does not outlive the frame jump",
                        node_file(state.1, expr),
                        node_start(state.1, expr),
                        node_end(state.1, expr),
                    );
                }
            }
        }
        // Argument expressions are always evaluated in non-tail position, so
        // they are walked with tail = 0 unconditionally: a self-recursive
        // call nested in an argument (e.g. `f(g(n - 1))`) is non-tail
        // recursion even when the outer call sits in tail position.
        tail_walk_expr_list(state, fn_node, node_d(state.1, expr));
    } else if kind == EXPR_MATCH {
        tail_walk_expr(state, fn_node, node_b(state.1, expr), 0);
        let arms = node_c(state.1, expr);
        let count = list_len(state.2, arms);
        let mut idx = 0i64;
        while idx < count {
            let arm = list_get(state.2, arms, idx);
            let body = node_b(state.1, arm);
            if body != NONE {
                tail_walk_stmt(state, fn_node, body, tail);
            }
            idx += 1;
        }
    } else if kind == EXPR_TRY {
        tail_walk_expr(state, fn_node, node_b(state.1, expr), 0);
    } else if kind == EXPR_UNARY {
        tail_walk_expr(state, fn_node, node_c(state.1, expr), 0);
    } else if kind == EXPR_BINARY {
        tail_walk_expr(state, fn_node, node_c(state.1, expr), 0);
        tail_walk_expr(state, fn_node, node_d(state.1, expr), 0);
    } else if kind == EXPR_STRUCT_LIT {
        tail_walk_expr_list(state, fn_node, node_d(state.1, expr));
    } else if kind == EXPR_ARRAY {
        tail_walk_expr_list(state, fn_node, node_b(state.1, expr));
    } else if kind == EXPR_INDEX {
        tail_walk_expr(state, fn_node, node_b(state.1, expr), 0);
        tail_walk_expr(state, fn_node, node_c(state.1, expr), 0);
    } else if kind == EXPR_FIELD_ACCESS {
        tail_walk_expr(state, fn_node, node_b(state.1, expr), 0);
    }
}

fn tail_walk_expr_list(state: &mut State, fn_node: i64, list: i64) {
    let count = list_len(state.2, list);
    let mut idx = 0i64;
    while idx < count {
        tail_walk_expr(state, fn_node, list_get(state.2, list, idx), 0);
        idx += 1;
    }
}

fn check_stmt_list(state: &mut State, list: i64, ret: i64, impure: i64, self_key: i64) {
    let count = list_len(state.2, list);
    let mut idx = 0i64;
    while idx < count {
        check_stmt(state, list_get(state.2, list, idx), ret, impure, self_key);
        idx += 1;
    }
}

fn check_stmt(state: &mut State, stmt: i64, ret: i64, impure: i64, self_key: i64) -> i64 {
    if node_tag(state.1, stmt) != NODE_STMT {
        return unit_key_of(state);
    }
    attach_local_facts(state, stmt);
    let kind = node_a(state.1, stmt);
    let file = node_file(state.1, stmt);
    let start = node_start(state.1, stmt);
    let end = node_end(state.1, stmt);
    if kind == STMT_LET {
        let name = node_c(state.1, stmt);
        let is_mut = node_b(state.1, stmt);
        let declared = node_d(state.1, stmt);
        let init = node_e(state.1, stmt);
        let binding_key = if declared != NONE {
            let dkey = canon_ty(state, declared, self_key, 1);
            let ikey = check_expr(state, init, dkey, ret, impure, self_key);
            let ok = unify_key(state.1, state.2, state.6, ikey, dkey);
            if !ok && key_kind(state.1, ikey) != TYD_UNKNOWN && key_kind(state.1, dkey) != TYD_UNKNOWN {
                push_error(state.3, &format!("cannot assign '{}' to '{}'", render_key(state.0, state.1, state.2, state.6, state.7, ikey), render_key(state.0, state.1, state.2, state.6, state.7, dkey)), file, start, end);
                push_note_for_last(
                    state.3,
                    state.16,
                    "declared type here",
                    node_file(state.1, declared),
                    node_start(state.1, declared),
                    node_end(state.1, declared),
                    NOTE_CONTEXT,
                );
            }
            dkey
        } else {
            check_expr(state, init, NONE, ret, impure, self_key)
        };
        bind(state.4, name, binding_key, is_mut, stmt);
        stmt_set_ty(state.1, stmt, binding_key);
        return binding_key;
    }
    if kind == STMT_ASSIGN {
        let target = node_b(state.1, stmt);
        let value = node_c(state.1, stmt);
        let tkey = check_assign_target(state, target, ret, impure, self_key);
        let vkey = check_expr(state, value, tkey, ret, impure, self_key);
        let ok = unify_key(state.1, state.2, state.6, vkey, tkey);
        if !ok && key_kind(state.1, vkey) != TYD_UNKNOWN && key_kind(state.1, tkey) != TYD_UNKNOWN {
            push_error(state.3, &format!("cannot assign '{}' to '{}'", render_key(state.0, state.1, state.2, state.6, state.7, vkey), render_key(state.0, state.1, state.2, state.6, state.7, tkey)), file, start, end);
            let declared_ty = assign_target_declared_type(state, target);
            if declared_ty != NONE {
                push_note_for_last(
                    state.3,
                    state.16,
                    "declared type here",
                    node_file(state.1, declared_ty),
                    node_start(state.1, declared_ty),
                    node_end(state.1, declared_ty),
                    NOTE_CONTEXT,
                );
            }
        }
        stmt_set_ty(state.1, stmt, tkey);
        return tkey;
    }
    if kind == STMT_WHILE {
        let cond = check_expr(state, node_b(state.1, stmt), NONE, ret, impure, self_key);
        if !is_bool_key(state.1, cond) {
            push_error(state.3, "while condition must be Bool", file, start, end);
        }
        push_scope(state.4);
        state.14 += 1;
        check_stmt_list(state, node_c(state.1, stmt), ret, impure, self_key);
        state.14 -= 1;
        pop_scope(state.4);
        let unit = unit_key_of(state);
        stmt_set_ty(state.1, stmt, unit);
        return unit;
    }
    if kind == STMT_IF {
        let cond = check_expr(state, node_b(state.1, stmt), NONE, ret, impure, self_key);
        if !is_bool_key(state.1, cond) {
            push_error(state.3, "if condition must be Bool", file, start, end);
        }
        push_scope(state.4);
        check_stmt_list(state, node_c(state.1, stmt), ret, impure, self_key);
        pop_scope(state.4);
        if node_d(state.1, stmt) != NONE {
            push_scope(state.4);
            check_stmt_list(state, node_d(state.1, stmt), ret, impure, self_key);
            pop_scope(state.4);
        }
        let unit = unit_key_of(state);
        stmt_set_ty(state.1, stmt, unit);
        return unit;
    }
    if kind == STMT_RETURN {
        let value = node_b(state.1, stmt);
        let key;
        if value == NONE {
            if !is_unit_key(state.1, ret) {
                push_error(state.3, &format!("return with no value in a function returning '{}'", render_key(state.0, state.1, state.2, state.6, state.7, ret)), file, start, end);
            }
            key = unit_key_of(state);
        } else {
            key = check_expr(state, value, ret, ret, impure, self_key);
            let ok = unify_key(state.1, state.2, state.6, key, ret);
            if !ok && key_kind(state.1, key) != TYD_UNKNOWN && key_kind(state.1, ret) != TYD_UNKNOWN {
                push_error(state.3, &format!("return type mismatch: expected '{}', found '{}'", render_key(state.0, state.1, state.2, state.6, state.7, ret), render_key(state.0, state.1, state.2, state.6, state.7, key)), file, start, end);
                if state.17 != NONE {
                    push_note_for_last(
                        state.3,
                        state.16,
                        "declared return type here",
                        node_file(state.1, state.17),
                        node_start(state.1, state.17),
                        node_end(state.1, state.17),
                        NOTE_CONTEXT,
                    );
                }
            }
        }
        stmt_set_ty(state.1, stmt, key);
        return key;
    }
    if kind == STMT_BREAK || kind == STMT_CONTINUE {
        if state.14 == 0 {
            let what = if kind == STMT_BREAK { "break" } else { "continue" };
            push_error(state.3, &format!("{} outside of a loop", what), file, start, end);
        }
        let unit = unit_key_of(state);
        stmt_set_ty(state.1, stmt, unit);
        return unit;
    }
    let expr = node_b(state.1, stmt);
    let key = check_expr(state, expr, NONE, ret, impure, self_key);
    if is_result_key(state.1, key) {
        push_error(state.3, "unhandled Result value: use try or match", file, start, end);
        let origin = call_result_origin(state, expr);
        if origin != NONE {
            push_note_for_last(
                state.3,
                state.16,
                "declared return type here",
                node_file(state.1, origin),
                node_start(state.1, origin),
                node_end(state.1, origin),
                NOTE_CONTEXT,
            );
        }
    } else if is_option_key(state.1, key) {
        push_error(state.3, "unhandled Option value: use try or match", file, start, end);
        let origin = call_result_origin(state, expr);
        if origin != NONE {
            push_note_for_last(
                state.3,
                state.16,
                "declared return type here",
                node_file(state.1, origin),
                node_start(state.1, origin),
                node_end(state.1, origin),
                NOTE_CONTEXT,
            );
        }
    }
    stmt_set_ty(state.1, stmt, key);
    key
}

// The scope the resolver attached to `source` (a SCOPE_AT fact), so a
// suggestion reads the scope the resolver already computed rather than
// reconstructing one.
fn scope_of(nodes: &[i64], source: i64) -> i64 {
    let count = nodes.len() as i64 / NODE_STRIDE;
    let mut idx = 0i64;
    while idx < count {
        if node_tag(nodes, idx) == NODE_SCOPEFACT
            && node_a(nodes, idx) == SCOPE_AT
            && node_b(nodes, idx) == source
        {
            return node_c(nodes, idx);
        }
        idx += 1;
    }
    NONE
}

// The return-type node of the function a call resolves to, when the call's
// Result/Option value is directly that function's return value.  A division
// or index result has no declared function to point at, so it yields NONE.
fn call_result_origin(state: &mut State, expr: i64) -> i64 {
    if node_tag(state.1, expr) != NODE_EXPR || node_a(state.1, expr) != EXPR_CALL {
        return NONE;
    }
    let callee = node_b(state.1, expr);
    if node_tag(state.1, callee) != NODE_EXPR || node_a(state.1, callee) != EXPR_PATH {
        return NONE;
    }
    let sym = expr_sym_of(state.1, callee);
    if sym == NONE {
        return NONE;
    }
    let kind = sym_kind(state.1, sym);
    if kind != SYM_FUN && kind != SYM_NATIVE_FUN {
        return NONE;
    }
    let decl = sym_decl(state.1, sym);
    if decl == NONE || node_tag(state.1, decl) != NODE_ITEM {
        return NONE;
    }
    let fn_node = node_d(state.1, decl);
    let ret_ty = node_d(state.1, fn_node);
    if node_file(state.1, ret_ty) == NO_FILE {
        return NONE;
    }
    ret_ty
}

// The declared type node of the binding an assignment target names, when the
// target is a bare local with a declared type (`var x: I64 = ...`).
fn assign_target_declared_type(state: &mut State, target: i64) -> i64 {
    if node_tag(state.1, target) != NODE_EXPR || node_a(state.1, target) != EXPR_PATH {
        return NONE;
    }
    let segs = node_b(state.1, target);
    if list_len(state.2, segs) != 1 {
        return NONE;
    }
    let name = list_first(state.2, segs);
    let full = lookup_full(state.4, name);
    let decl = full.2;
    if decl != NONE && node_tag(state.1, decl) == NODE_STMT && node_a(state.1, decl) == STMT_LET && node_d(state.1, decl) != NONE {
        return node_d(state.1, decl);
    }
    NONE
}

// Offer a hedged "did you mean" note for an unresolved value name, drawn
// from the locals in the live environment and the value-namespace names the
// resolver materialized for the source's scope.  The error must already be
// pushed so the note attaches to it.
fn suggest_value_name(state: &mut State, source: i64, misspelled: i64) {
    let text = name_text(state.0, misspelled);
    let mut entries: Vec<(String, i64, i64, i64)> = Vec::new();
    let mut seen: Vec<String> = Vec::new();
    let mut depth = state.4.len();
    while depth > 0 {
        depth -= 1;
        match state.4.get(depth) {
            Some(scope) => {
                let mut idx = 0i64;
                while idx < scope.len() as i64 / 4 {
                    let name = entry_at(scope, idx, 0);
                    let decl = entry_at(scope, idx, 3);
                    let text_name = name_text(state.0, name);
                    if decl != NONE && node_file(state.1, decl) != NO_FILE && !seen.contains(&text_name) {
                        seen.push(text_name.clone());
                        entries.push((text_name, node_file(state.1, decl), node_start(state.1, decl), node_end(state.1, decl)));
                    }
                    idx += 1;
                }
            }
            None => break,
        }
    }
    let scope = scope_of(state.1, source);
    let count = state.1.len() as i64 / NODE_STRIDE;
    let mut nidx = 0i64;
    while nidx < count {
        if node_tag(state.1, nidx) == NODE_SCOPEFACT
            && node_a(state.1, nidx) == SCOPE_VISIBLE
            && node_b(state.1, nidx) == scope
            && node_e(state.1, nidx) == NS_VALUE
        {
            let name = node_c(state.1, nidx);
            let sym = node_d(state.1, nidx);
            let decl = sym_decl(state.1, sym);
            let text_name = name_text(state.0, name);
            if decl != NONE && node_tag(state.1, decl) == NODE_ITEM && node_file(state.1, decl) != NO_FILE && !seen.contains(&text_name) {
                seen.push(text_name.clone());
                entries.push((text_name, node_file(state.1, decl), node_start(state.1, decl), node_end(state.1, decl)));
            }
        }
        nidx += 1;
    }
    let mut candidates: Vec<suggest::Candidate> = Vec::new();
    let mut idx = 0usize;
    while idx < entries.len() {
        match entries.get(idx) {
            Some(entry) => {
                candidates.push(suggest::Candidate {
                    name: entry.0.clone(),
                    file: entry.1,
                    start: entry.2,
                    end: entry.3,
                });
            }
            None => break,
        }
        idx += 1;
    }
    if let Some(suggestion) = suggest::suggest(&text, &candidates) {
        push_note_for_last(state.3, state.16, &suggestion.message, suggestion.file, suggestion.start, suggestion.end, NOTE_GUIDANCE);
    }
}

fn collect_consts(state: &mut State, list: i64) {
    let count = list_len(state.2, list);
    let mut idx = 0i64;
    while idx < count {
        collect_const_item(state, list_get(state.2, list, idx));
        idx += 1;
    }
}

fn collect_const_item(state: &mut State, item: i64) {
    if node_tag(state.1, item) != NODE_ITEM {
        return;
    }
    let kind = node_a(state.1, item);
    if kind == ITEM_MODULE {
        collect_consts(state, node_e(state.1, item));
        return;
    }
    if kind != ITEM_CONST {
        return;
    }
    let sym = item_sym_of(state.1, item);
    let decl_ty = node_e(state.1, item);
    let declared = canon_ty(state, decl_ty, NONE, 1);
    let value_expr = node_f(state.1, item);
    let file = node_file(state.1, item);
    let start = node_start(state.1, item);
    let end = node_end(state.1, item);
    let (value, key) = fold_const(state, value_expr, declared, 0);
    let ok = unify_key(state.1, state.2, state.6, key, declared);
    // A folded key of TYD_UNKNOWN (or a declared key that failed to
    // resolve) means the initializer already produced its primary
    // diagnostic; the mismatch below would be a "found '?'" cascade, so it
    // is suppressed (Single-Fact: fold_const owns the error return key).
    if !ok && key_kind(state.1, key) != TYD_UNKNOWN && key_kind(state.1, declared) != TYD_UNKNOWN {
        push_error(state.3, &format!("constant initializer type mismatch: expected '{}', found '{}'", render_key(state.0, state.1, state.2, state.6, state.7, declared), render_key(state.0, state.1, state.2, state.6, state.7, key)), file, start, end);
        push_note_for_last(
            state.3,
            state.16,
            "declared type here",
            node_file(state.1, decl_ty),
            node_start(state.1, decl_ty),
            node_end(state.1, decl_ty),
            NOTE_CONTEXT,
        );
    }
    alloc_node(state.1, &[NODE_CONSTVAL, NO_FILE, NO_FILE, NO_FILE, sym, value, NONE, NONE, NONE, NONE]);
    expr_set_ty(state.1, value_expr, key);
}

fn fold_const(state: &mut State, expr: i64, declared: i64, quiet: i64) -> (i64, i64) {
    if node_tag(state.1, expr) != NODE_EXPR {
        if quiet == 0 {
            push_error(state.3, "constant expression required", node_file(state.1, expr), node_start(state.1, expr), node_end(state.1, expr));
        }
        return (0, recover_ty(state, expr, declared));
    }
    let kind = node_a(state.1, expr);
    let file = node_file(state.1, expr);
    let start = node_start(state.1, expr);
    let end = node_end(state.1, expr);
    if kind == EXPR_LIT {
        let lit = node_b(state.1, expr);
        let value = node_c(state.1, expr);
        if lit == LIT_TRUE || lit == LIT_FALSE {
            return (value, builtin_key_of(state.1, BUILTIN_BOOL));
        }
        if lit == LIT_STRING {
            // A string constant folds to the interned name id of its bytes,
            // which is what codegen needs to emit (or reuse) the literal's
            // `.rodata` global — the same id an inline literal carries, so a
            // `const` string and an inline string are one representation.
            // There is no range to check: the value is a byte sequence.
            return (value, byte_slice_key(state));
        }
        let key = if is_int_key(state.1, declared) {
            declared
        } else {
            builtin_key_of(state.1, BUILTIN_I64)
        };
        if !range_check_literal(state, value, lit, 0, key, (file, start, end), quiet) {
            // The literal's value is out of range for the target width, but
            // its type recovers to the declared key (the expected type of
            // the constant), so collect_const_item's unify succeeds and the
            // range diagnostic is the only one emitted (no "found '?'"
            // cascade).  In a quiet probe the declared key is NONE and the
            // recovery is TYD_UNKNOWN, which probes treat as "not a
            // constant".
            return (value, recover_ty(state, expr, declared));
        }
        return (value, key);
    }
    if kind == EXPR_UNARY && node_b(state.1, expr) == UN_NEG {
        let operand = node_c(state.1, expr);
        // A negated literal is one atomic signed constant: the magnitude is
        // extracted raw from the child literal and negated in two's
        // complement, then range-checked once against the target width.  The
        // child literal is never evaluated as an independent positive value,
        // so a 64-bit pattern like 0xFFFFFFFFFFFFFF00 does not trip an I64
        // range error before the negation is applied.
        let target = if is_int_key(state.1, declared) {
            declared
        } else {
            builtin_key_of(state.1, BUILTIN_I64)
        };
        if node_tag(state.1, operand) == NODE_EXPR
            && node_a(state.1, operand) == EXPR_LIT
            && (node_b(state.1, operand) == LIT_INT || node_b(state.1, operand) == LIT_HEX)
        {
            if !key_is_signed(state.1, target) {
                if quiet == 0 {
                    push_error(state.3, "unary '-' is not allowed on unsigned integer types", file, start, end);
                }
                return (0, recover_ty(state, expr, target));
            }
            let magnitude = node_c(state.1, operand);
            let negated = magnitude.wrapping_neg();
            if !range_check_literal(state, negated, LIT_INT, 1, target, (file, start, end), quiet) {
                // The negated value is out of range for the target width, but
                // the constant still recovers to the target key, so the range
                // diagnostic is the only one emitted (no "found '?'" cascade).
                return (negated, recover_ty(state, expr, target));
            }
            return (negated, target);
        }
        // Non-literal operand: fold recursively, then negate and check.
        let (value, key) = fold_const(state, operand, NONE, quiet);
        if is_int_key(state.1, declared) && !key_is_signed(state.1, declared) {
            if quiet == 0 {
                push_error(state.3, "unary '-' is not allowed on unsigned integer types", file, start, end);
            }
            // The negation is rejected, but the constant still recovers to
            // the declared key, so the unsigned-negation diagnostic is the
            // only one emitted (no "found '?'" cascade).
            return (value, recover_ty(state, expr, declared));
        }
        if key_kind(state.1, key) == TYD_UNKNOWN {
            return (0, recover_ty(state, expr, declared));
        }
        let negated = value.wrapping_neg();
        if is_int_key(state.1, declared) {
            if !range_check_literal(state, negated, LIT_INT, 1, declared, (file, start, end), quiet) {
                // Same root cause as the atomic path: the magnitude is out of
                // range for the target width, but the type recovers to the
                // declared key, so the range diagnostic is the only one
                // emitted (no cascading "found '?'" secondary).
                return (negated, recover_ty(state, expr, declared));
            }
            return (negated, declared);
        }
        return (negated, key);
    }
    if kind == EXPR_PATH {
        let sym = expr_sym_of(state.1, expr);
        if sym != NONE && sym_kind(state.1, sym) == SYM_CONST {
            let item = sym_decl(state.1, sym);
            if !has_const_value(state.1, sym) {
                if quiet == 0 {
                    push_error(state.3, &format!("constant '{}' must be declared before use", name_text(state.0, node_d(state.1, item))), file, start, end);
                }
                return (0, recover_ty(state, expr, declared));
            }
            let value = find_const_value(state.1, sym);
            let key = ty_key_of(state.1, node_e(state.1, item));
            return (value, key);
        }
        if sym == NONE {
            // An unresolvable path: the resolver bound nothing, so the
            // diagnostic names the path's own segments instead of the
            // generic "constant expression required" (a truthful primary).
            let segs = list_to_vec(state.2, node_b(state.1, expr));
            let path_text = join_path(state.0, &segs);
            if quiet == 0 {
                if path_text.is_empty() {
                    push_error(state.3, "constant expression required", file, start, end);
                } else {
                    push_error(state.3, &format!("constant '{}' must be declared before use", path_text), file, start, end);
                }
            }
        } else if quiet == 0 {
            push_error(state.3, "constant expression required", file, start, end);
        }
        // The path failed in a typed constant initializer: the constant
        // recovers to the declared key so no "found '?'" cascade follows
        // the primary.
        return (0, recover_ty(state, expr, declared));
    }
    if kind == EXPR_BINARY {
        let op = node_b(state.1, expr);
        let lhs = node_c(state.1, expr);
        let rhs = node_d(state.1, expr);
        // The literal-typing rule, identical to `check_binary_operands`: an
        // operand that is only integer literals adopts the peer operand's
        // type when the peer has one, otherwise the type expected of this
        // operator's result.  A comparison declares `Bool`, which tells its
        // operands nothing, so there the operands type each other.  Keeping
        // this in step with the runtime path is what stops the same source
        // text from typing one way in a `const` and another in a `var`.
        let operand_declared = binary_operand_expected(state, op, declared);
        let lhs_untyped = int_literal_expr(state.1, lhs);
        let rhs_untyped = int_literal_expr(state.1, rhs);
        let folded = if lhs_untyped && !rhs_untyped {
            let (rv, rk) = fold_const(state, rhs, NONE, quiet);
            if key_kind(state.1, rk) == TYD_UNKNOWN {
                return (0, recover_ty(state, expr, declared));
            }
            let hint = if is_int_key(state.1, rk) { rk } else { operand_declared };
            let (lv, lk) = fold_const(state, lhs, hint, quiet);
            if key_kind(state.1, lk) == TYD_UNKNOWN {
                return (0, recover_ty(state, expr, declared));
            }
            ((lv, lk), (rv, rk))
        } else {
            let lhs_declared = if lhs_untyped { operand_declared } else { NONE };
            let (lv, lk) = fold_const(state, lhs, lhs_declared, quiet);
            if key_kind(state.1, lk) == TYD_UNKNOWN {
                return (0, recover_ty(state, expr, declared));
            }
            let rhs_declared = if is_int_key(state.1, lk) {
                lk
            } else if rhs_untyped {
                operand_declared
            } else {
                NONE
            };
            let (rv, rk) = fold_const(state, rhs, rhs_declared, quiet);
            if key_kind(state.1, rk) == TYD_UNKNOWN {
                return (0, recover_ty(state, expr, declared));
            }
            ((lv, lk), (rv, rk))
        };
        let ((lv, lk), (rv, rk)) = folded;
        let ok = unify_key(state.1, state.2, state.6, lk, rk);
        if !ok {
            if quiet == 0 {
                push_error(state.3, "constant operands have different types", file, start, end);
            }
            return (0, recover_ty(state, expr, declared));
        }
        let (v, k) = fold_bin(state, op, lv, rv, lk, (file, start, end), quiet);
        if key_kind(state.1, k) == TYD_UNKNOWN && quiet == 0 {
            // fold_bin already emitted the primary diagnostic; the constant
            // still recovers to the declared key so no "found '?'" cascade
            // follows.
            return (0, recover_ty(state, expr, declared));
        }
        return (v, k);
    }
    if quiet == 0 {
        push_error(state.3, "constant expression required", file, start, end);
    }
    (0, recover_ty(state, expr, declared))
}

fn euclid_div_i64(lv: i64, rv: i64) -> i64 {
    let rem = lv.wrapping_rem(rv);
    let euclid_rem = if rem < 0 {
        if rv > 0 {
            rem.wrapping_add(rv)
        } else {
            rem.wrapping_sub(rv)
        }
    } else {
        rem
    };
    lv.wrapping_sub(euclid_rem).wrapping_div(rv)
}

fn euclid_rem_i64(lv: i64, rv: i64) -> i64 {
    let rem = lv.wrapping_rem(rv);
    if rem < 0 {
        if rv > 0 {
            rem.wrapping_add(rv)
        } else {
            rem.wrapping_sub(rv)
        }
    } else {
        rem
    }
}

// Sign-extends the low `width` bits of `value` to a full i64.
fn sext_int(value: u64, width: u32) -> i64 {
    if width >= 64 {
        value as i64
    } else {
        let mask = (1u64 << width) - 1;
        let bits = value & mask;
        let sign = (bits >> (width - 1)) & 1;
        if sign == 1 { (bits | !mask) as i64 } else { bits as i64 }
    }
}

// Keeps only the low `width` bits of `value`.
fn mask_int(value: u64, width: u32) -> u64 {
    if width >= 64 { value } else { value & ((1u64 << width) - 1) }
}

// The constant folder is width- and signedness-aware so folded constants
// agree with runtime at every width: signed operands are sign-extended and
// shifted/comparisoned arithmetically, unsigned operands are masked and
// shifted/comparisoned logically, results are stored as the width-masked
// bit pattern (codegen's const emission masks again), and shift counts are
// masked by the width.  Euclidean division and the defined `MIN / -1` edge
// hold for every signed width.
fn fold_bin(state: &mut State, op: i64, lv: i64, rv: i64, key: i64, span: (i64, i64, i64), quiet: i64) -> (i64, i64) {
    let (file, start, end) = span;
    let bool_key = builtin_key_of(state.1, BUILTIN_BOOL);
    if op == BIN_AND || op == BIN_OR {
        // `check_binary` requires Bool operands for `&&`/`||`; folding must
        // enforce the identical rule; otherwise `const C: Bool = 1 && 2`
        // (folds `1 & 2` as if they were already Bool) and `val c: Bool = 1
        // && 2` (rejected by check_binary) would disagree on the exact same
        // source text, which is the divergence the literal-typing rule was
        // written to rule out everywhere.
        if !is_bool_key(state.1, key) {
            if quiet == 0 {
                push_error(state.3, &format!("logical operator '{}' requires Bool operands", op_text(op)), file, start, end);
            }
            return (0, unknown_key(state.1, state.2));
        }
        if op == BIN_AND {
            return (lv & rv, bool_key);
        }
        return (lv | rv, bool_key);
    }
    let sub = tyinfo_builtin_kind(state.1, key);
    let width = builtin_int_width(sub);
    if width == 0 {
        // `Bool` equality is well-defined on the raw 0/1 values even though
        // Bool has no integer width, so it folds here; `comparable_key` is
        // the same predicate `check_binary` applies, so a constant and a
        // runtime expression agree on exactly which comparisons exist.
        // Every other non-integer operand is rejected below rather than
        // folded, and the diagnostic is re-reported in non-quiet mode so
        // the constant is refused truthfully instead of failing
        // unification against '?'.
        if comparable_key(state.1, key, op) {
            if op == BIN_EQ {
                return ((lv == rv) as i64, bool_key);
            }
            return ((lv != rv) as i64, bool_key);
        }
        if quiet == 0 {
            let message = if (BIN_EQ..=BIN_GE).contains(&op) {
                format!("comparison '{}' is not defined for '{}': compare integer or Bool values, or take the value apart with match", op_text(op), render_key(state.0, state.1, state.2, state.6, state.7, key))
            } else {
                format!("constant binary operator '{}' requires integer operands", op_text(op))
            };
            push_error(state.3, &message, file, start, end);
        }
        return (0, unknown_key(state.1, state.2));
    }
    let signed = builtin_int_is_signed(sub);
    let mask = builtin_int_mask(sub);
    if signed {
        let a = sext_int(lv as u64, width);
        let b = sext_int(rv as u64, width);
        let amount = (rv as u64 % width as u64) as u32;
        if op == BIN_ADD {
            return (mask_int(a.wrapping_add(b) as u64, width) as i64, key);
        }
        if op == BIN_SUB {
            return (mask_int(a.wrapping_sub(b) as u64, width) as i64, key);
        }
        if op == BIN_MUL {
            return (mask_int(a.wrapping_mul(b) as u64, width) as i64, key);
        }
        if op == BIN_DIV {
            if b == 0 {
                if quiet == 0 {
                    push_error(state.3, "division by zero in constant", file, start, end);
                }
                return (0, unknown_key(state.1, state.2));
            }
            return (mask_int(euclid_div_i64(a, b) as u64, width) as i64, key);
        }
        if op == BIN_MOD {
            if b == 0 {
                if quiet == 0 {
                    push_error(state.3, "modulo by zero in constant", file, start, end);
                }
                return (0, unknown_key(state.1, state.2));
            }
            return (mask_int(euclid_rem_i64(a, b) as u64, width) as i64, key);
        }
        if op == BIN_SHL {
            return (mask_int(a.wrapping_shl(amount) as u64, width) as i64, key);
        }
        if op == BIN_SHR {
            return (mask_int((a >> amount) as u64, width) as i64, key);
        }
        if op == BIN_BAND {
            return (mask_int((a & b) as u64, width) as i64, key);
        }
        if op == BIN_BOR {
            return (mask_int((a | b) as u64, width) as i64, key);
        }
        if op == BIN_BXOR {
            return (mask_int((a ^ b) as u64, width) as i64, key);
        }
        // Signed comparisons sign-extend the stored (width-masked) values
        // before ordering them, so a negative arithmetic result stored as
        // its masked bit pattern (I8 `-1 + 0` -> 255) still compares as
        // -1, agreeing with runtime.
        if op == BIN_EQ {
            return ((a == b) as i64, bool_key);
        }
        if op == BIN_NE {
            return ((a != b) as i64, bool_key);
        }
        if op == BIN_LT {
            return ((a < b) as i64, bool_key);
        }
        if op == BIN_GT {
            return ((a > b) as i64, bool_key);
        }
        if op == BIN_LE {
            return ((a <= b) as i64, bool_key);
        }
        if op == BIN_GE {
            return ((a >= b) as i64, bool_key);
        }
    } else {
        let a = lv as u64 & mask;
        let b = rv as u64 & mask;
        let amount = (rv as u64 % width as u64) as u32;
        if op == BIN_ADD {
            return ((a.wrapping_add(b) & mask) as i64, key);
        }
        if op == BIN_SUB {
            return ((a.wrapping_sub(b) & mask) as i64, key);
        }
        if op == BIN_MUL {
            return ((a.wrapping_mul(b) & mask) as i64, key);
        }
        if op == BIN_DIV {
            if b == 0 {
                if quiet == 0 {
                    push_error(state.3, "division by zero in constant", file, start, end);
                }
                return (0, unknown_key(state.1, state.2));
            }
            return (((a / b) & mask) as i64, key);
        }
        if op == BIN_MOD {
            if b == 0 {
                if quiet == 0 {
                    push_error(state.3, "modulo by zero in constant", file, start, end);
                }
                return (0, unknown_key(state.1, state.2));
            }
            return (((a % b) & mask) as i64, key);
        }
        if op == BIN_SHL {
            return ((a.wrapping_shl(amount) & mask) as i64, key);
        }
        if op == BIN_SHR {
            return ((a >> amount) as i64, key);
        }
        if op == BIN_BAND {
            return ((a & b) as i64, key);
        }
        if op == BIN_BOR {
            return ((a | b) as i64, key);
        }
        if op == BIN_BXOR {
            return ((a ^ b) as i64, key);
        }
        // Unsigned comparisons order the width-masked values directly; the
        // stored bit pattern is already the true unsigned value.
        if op == BIN_EQ {
            return ((a == b) as i64, bool_key);
        }
        if op == BIN_NE {
            return ((a != b) as i64, bool_key);
        }
        if op == BIN_LT {
            return ((a < b) as i64, bool_key);
        }
        if op == BIN_GT {
            return ((a > b) as i64, bool_key);
        }
        if op == BIN_LE {
            return ((a <= b) as i64, bool_key);
        }
        if op == BIN_GE {
            return ((a >= b) as i64, bool_key);
        }
    }
    if quiet == 0 {
        push_error(state.3, "unknown constant operator", file, start, end);
    }
    (0, unknown_key(state.1, state.2))
}

fn check_expr(state: &mut State, expr: i64, expected: i64, ret: i64, impure: i64, self_key: i64) -> i64 {
    if node_tag(state.1, expr) != NODE_EXPR {
        return unknown_key(state.1, state.2);
    }
    attach_local_facts(state, expr);
    let kind = node_a(state.1, expr);
    if kind == EXPR_LIT {
        return check_lit(state, expr, expected);
    }
    if kind == EXPR_PATH {
        return check_path(state, expr, expected);
    }
    if kind == EXPR_UNARY {
        return check_unary(state, expr, expected, ret, impure, self_key);
    }
    if kind == EXPR_BINARY {
        return check_binary(state, expr, expected, ret, impure, self_key);
    }
    if kind == EXPR_CALL {
        return check_call(state, expr, expected, ret, impure, self_key);
    }
    if kind == EXPR_STRUCT_LIT {
        return check_struct_lit(state, expr, expected, ret, impure, self_key);
    }
    if kind == EXPR_ARRAY {
        return check_array(state, expr, expected, ret, impure, self_key);
    }
    if kind == EXPR_MATCH {
        return check_match(state, expr, expected, ret, impure, self_key);
    }
    if kind == EXPR_TRY {
        return check_try(state, expr, expected, ret, impure, self_key);
    }
    if kind == EXPR_INDEX {
        return check_index(state, expr, 0, expected, ret, impure, self_key);
    }
    if kind == EXPR_FIELD_ACCESS {
        return check_field_access(state, expr, expected, ret, impure, self_key);
    }
    push_error(state.3, "malformed expression", node_file(state.1, expr), node_start(state.1, expr), node_end(state.1, expr));
    recover_ty(state, expr, expected)
}

// The type of a string literal: `&[U8]`, a shared borrow of a byte slice.
//
// A literal's bytes live in the binary's read-only data for the whole run,
// so the borrow has no owner to outlive: there is nothing to consume,
// nothing to free, and no lifetime to track.  `&[U8]` rather than a
// dedicated string type because the byte slice is the representation the
// rest of the language already has — `Slice.len`, indexing, and
// `Collections.string_from_slice` all work on it unchanged.
fn byte_slice_key(state: &mut State) -> i64 {
    let byte = builtin_key_of(state.1, BUILTIN_U8);
    let slice = canon_tyinfo(state.1, state.2, TYD_SLICE, NONE, NONE, byte, NONE);
    canon_tyinfo(state.1, state.2, TYD_REF, NONE, NONE, slice, NONE)
}

fn check_lit(state: &mut State, expr: i64, expected: i64) -> i64 {
    let lit = node_b(state.1, expr);
    if lit == LIT_TRUE || lit == LIT_FALSE {
        let key = builtin_key_of(state.1, BUILTIN_BOOL);
        expr_set_ty(state.1, expr, key);
        return key;
    }
    if lit == LIT_STRING {
        // A string literal has one type and adopts nothing: unlike an
        // integer literal it is not a width-agnostic magnitude, so an
        // expected type of anything else is a mismatch the caller reports.
        let key = byte_slice_key(state);
        expr_set_ty(state.1, expr, key);
        return key;
    }
    let key = if is_int_key(state.1, expected) {
        expected
    } else {
        builtin_key_of(state.1, BUILTIN_I64)
    };
    let value = node_c(state.1, expr);
    let file = node_file(state.1, expr);
    let start = node_start(state.1, expr);
    let end = node_end(state.1, expr);
    if !range_check_literal(state, value, lit, 0, key, (file, start, end), 0) {
        // The literal is out of range for the width it was adopted into;
        // its type recovers to the expected key (or TYD_UNKNOWN when none
        // is known) so the range diagnostic is the only one emitted.
        return recover_ty(state, expr, expected);
    }
    expr_set_ty(state.1, expr, key);
    key
}

// Rejects an integer literal whose magnitude does not fit the width and
// signedness of `key` (the type it is being adopted into).  `lit` picks the
// diagnostic spelling (hex vs decimal); `negated` marks a value produced by
// unary negation, which is displayed signed and checked against the signed
// half of the width.  Quiet probes never report.
fn range_check_literal(state: &mut State, value: i64, lit: i64, negated: i64, key: i64, span: (i64, i64, i64), quiet: i64) -> bool {
    let (file, start, end) = span;
    if key_kind(state.1, key) != TYD_BUILTIN {
        return true;
    }
    let sub = tyinfo_builtin_kind(state.1, key);
    let width = builtin_int_width(sub);
    if width == 0 {
        return true;
    }
    let bits = value as u64;
    let ok = if builtin_int_is_signed(sub) {
        if negated == 1 {
            // A negated literal must be non-positive and within the target
            // type's negative range.  `value` is the wrapping_neg of the
            // literal's magnitude, so an out-of-range hex magnitude can wrap
            // positive (e.g. `-0xFFFFFFFFFFFFFF00` -> 256); the upper bound
            // catches those, the lower bound the genuinely too-negative ones.
            let min_val = -(1i128 << (width - 1));
            let v128 = value as i128;
            v128 <= 0 && v128 >= min_val
        } else {
            bits < (1u64 << (width - 1))
        }
    } else {
        bits <= builtin_int_mask(sub)
    };
    if !ok && quiet == 0 {
        let shown = if negated == 1 {
            format!("{}", value as i128)
        } else if lit == LIT_HEX {
            format!("0x{:X}", bits)
        } else {
            format!("{}", bits)
        };
        push_error(state.3, &format!("integer literal {} is out of range for '{}'", shown, render_key(state.0, state.1, state.2, state.6, state.7, key)), file, start, end);
    }
    ok
}

fn check_unary(state: &mut State, expr: i64, expected: i64, ret: i64, impure: i64, self_key: i64) -> i64 {
    let op = node_b(state.1, expr);
    let operand = node_c(state.1, expr);
    let file = node_file(state.1, expr);
    let start = node_start(state.1, expr);
    let end = node_end(state.1, expr);
    let key;
    if (op == UN_REF || op == UN_REF_MUT) && node_tag(state.1, operand) == NODE_EXPR && node_a(state.1, operand) == EXPR_INDEX {
        let borrow = if op == UN_REF { 1 } else { 2 };
        key = check_index(state, operand, borrow, expected, ret, impure, self_key);
    } else {
        let inner = check_expr(state, operand, NONE, ret, impure, self_key);
    if op == UN_REF || op == UN_REF_MUT {
        // The sanctioned array-to-slice coercion, in both borrow forms:
        // `&arr` is `&[T]` and `&mut arr` is `&mut [T]`.  Borrowing an
        // array never yields `&[T; N]` — the length travels in the slice
        // view instead of in the type — and there is no reason for the
        // exclusive borrow to behave differently from the shared one.  A
        // `&mut [T]` is what lets a caller hand a fixed-size buffer to a
        // native that fills it, which is how `File.read` receives one.
        let borrow = if op == UN_REF { TYD_REF } else { TYD_REF_MUT };
        let target = if key_kind(state.1, inner) == TYD_ARRAY {
            let elem = key_elem(state.1, inner);
            canon_tyinfo(state.1, state.2, TYD_SLICE, NONE, NONE, elem, NONE)
        } else {
            inner
        };
        key = canon_tyinfo(state.1, state.2, borrow, NONE, NONE, target, NONE);
        } else if op == UN_NEG {
            let inner_is_int = is_int_key(state.1, inner);
            if !inner_is_int {
                push_error(state.3, "unary '-' requires an integer operand", file, start, end);
            }
            // Only a bare integer-literal operand is untyped and may adopt
            // the expected width (`-5` types as I8 in `val x: I8 = -5`); a
            // typed value (a path, call, index, field access, ...) already
            // has a type and must never adopt another one through negation
            // — that is exactly the implicit conversion the literal-typing
            // rule forbids for every other operator, and unary '-' is not
            // an exception.
            let literal_operand = int_literal_expr(state.1, operand);
            if literal_operand && expected != NONE && is_int_key(state.1, expected) {
                // The negated literal adopts the expected width, so `-5` types
                // as I8 in `val x: I8 = -5`; only signed widths may be negated.
                if !key_is_signed(state.1, expected) {
                    push_error(state.3, "unary '-' is not allowed on unsigned integer types", file, start, end);
                    key = recover_ty(state, expr, expected);
                } else {
                    let (value, vkey) = fold_const(state, operand, NONE, 1);
                    if key_kind(state.1, vkey) != TYD_UNKNOWN {
                        range_check_literal(state, value.wrapping_neg(), LIT_INT, 1, expected, (file, start, end), 0);
                    }
                    key = expected;
                }
            } else if inner_is_int {
                if !key_is_signed(state.1, inner) {
                    push_error(state.3, "unary '-' is not allowed on unsigned integer types", file, start, end);
                    key = recover_ty(state, expr, expected);
                } else {
                    key = inner;
                }
            } else {
                key = recover_ty(state, expr, expected);
            }
        } else {
            if !is_bool_key(state.1, inner) {
                push_error(state.3, "unary '!' requires a Bool operand", file, start, end);
                key = recover_ty(state, expr, expected);
            } else {
                key = inner;
            }
        }
    }
    expr_set_ty(state.1, expr, key);
    key
}


// True when an expression is built out of nothing but integer literals,
// unary negation, and integer-valued binary operators.  Such an expression
// carries no type of its own — it is a width-agnostic magnitude — so it
// adopts the type its context demands (MANIFESTO, "Types": integer literals
// adopt the expected type in a typed context).  Every other expression form
// (path, call, index, field access, match, try, struct literal, array) has a
// declared or inferred type of its own and never adopts one; making a typed
// *value* take another width would be the implicit conversion the manifesto
// forbids.
//
// Comparison and logical operators are excluded because they yield `Bool`,
// not an integer, however their own operands are typed.
fn int_literal_expr(nodes: &[i64], expr: i64) -> bool {
    if node_tag(nodes, expr) != NODE_EXPR {
        return false;
    }
    let kind = node_a(nodes, expr);
    if kind == EXPR_LIT {
        let lit = node_b(nodes, expr);
        return lit == LIT_INT || lit == LIT_HEX;
    }
    if kind == EXPR_UNARY {
        return node_b(nodes, expr) == UN_NEG && int_literal_expr(nodes, node_c(nodes, expr));
    }
    if kind == EXPR_BINARY {
        let op = node_b(nodes, expr);
        if (BIN_EQ..=BIN_GE).contains(&op) || op == BIN_AND || op == BIN_OR {
            return false;
        }
        return int_literal_expr(nodes, node_c(nodes, expr)) && int_literal_expr(nodes, node_d(nodes, expr));
    }
    false
}

// The integer type a binary operator's *operands* are expected to have,
// derived from the type expected of the operator's result.  A comparison or
// logical operator yields `Bool`, which constrains its operands not at all,
// so it contributes no expectation and the operands type each other.  Every
// integer operator yields the operand type itself, so the expectation passes
// straight through — except that `/` and `%` wrap it: they evaluate to
// `Result(T, DivError)` at runtime, so an expected Result names the operand
// type in its `Ok` payload.  A constant initializer whose division the
// folder collapses declares `T` directly, and that shape is read straight
// through like any other operator's; both spellings name the same `T`.
fn binary_operand_expected(state: &mut State, op: i64, expected: i64) -> i64 {
    if expected == NONE || op == BIN_AND || op == BIN_OR || (BIN_EQ..=BIN_GE).contains(&op) {
        return NONE;
    }
    let result = if (op == BIN_DIV || op == BIN_MOD) && is_result_key(state.1, expected) {
        list_get(state.2, key_args(state.1, expected), 0)
    } else {
        expected
    };
    if is_int_key(state.1, result) { result } else { NONE }
}

fn check_static_zero_divisor(state: &mut State, op: i64, rhs: i64) -> i64 {
    if op != BIN_DIV && op != BIN_MOD {
        return 0;
    }
    let (value, key) = fold_const(state, rhs, NONE, 1);
    // Only an *integer* constant divisor can be a provable zero.  A folded
    // `Bool` carries 0 for `false` and a folded string carries an interned
    // name id, neither of which is a numeric zero; reporting either as a
    // division by zero would replace the real operand-type diagnostic with
    // a false one.
    if is_int_key(state.1, key) && value == 0 {
        let message = if op == BIN_DIV {
            "division by zero"
        } else {
            "modulo by zero"
        };
        push_error(state.3, message, node_file(state.1, rhs), node_start(state.1, rhs), node_end(state.1, rhs));
        1
    } else {
        0
    }
}

fn division_result_key(state: &mut State, payload: i64) -> i64 {
    let err_sym = state.11;
    if err_sym == NONE {
        return unknown_key(state.1, state.2);
    }
    let err_key = canon_tyinfo(state.1, state.2, TYD_ENUM, err_sym, NONE, NONE, NONE);
    let result_sym = state.9;
    if result_sym == NONE {
        return unknown_key(state.1, state.2);
    }
    let args = alloc_list(state.2);
    list_push(state.2, args, payload);
    list_push(state.2, args, err_key);
    canon_tyinfo(state.1, state.2, TYD_ENUM, result_sym, args, NONE, NONE)
}

// Checks a binary operator's two operands under the literal-typing rule.
// An operand that is only integer literals has no type of its own, so it
// adopts one from its context: the peer operand's type when the peer has
// one, otherwise the type expected of the operator's result, otherwise the
// `I64` default.  Whichever operand is typed is therefore checked first, so
// `255 != narrowed` types exactly like `narrowed != 255`.  An operand that
// is *not* a bare literal expression is never handed the result's expected
// type: it already has a type, and reporting it against a foreign
// expectation would emit a cascade ahead of the real operand-mismatch or
// assignment diagnostic.
//
// `fold_const`'s `EXPR_BINARY` arm applies the identical rule to constant
// initializers; the two must agree, or the same source text would type one
// way in a `const` and another in a `var`.
fn check_binary_operands(state: &mut State, operands: (i64, i64, i64), ret: i64, impure: i64, self_key: i64) -> (i64, i64) {
    let (lhs, rhs, operand_expected) = operands;
    let lhs_untyped = int_literal_expr(state.1, lhs);
    let rhs_untyped = int_literal_expr(state.1, rhs);
    if lhs_untyped && !rhs_untyped {
        let r = check_expr(state, rhs, NONE, ret, impure, self_key);
        let hint = if is_int_key(state.1, r) { r } else { operand_expected };
        let l = check_expr(state, lhs, hint, ret, impure, self_key);
        return (l, r);
    }
    let lhs_expected = if lhs_untyped { operand_expected } else { NONE };
    let l = check_expr(state, lhs, lhs_expected, ret, impure, self_key);
    let rhs_expected = if is_int_key(state.1, l) {
        l
    } else if rhs_untyped {
        operand_expected
    } else {
        NONE
    };
    let r = check_expr(state, rhs, rhs_expected, ret, impure, self_key);
    (l, r)
}

fn check_binary(state: &mut State, expr: i64, expected: i64, ret: i64, impure: i64, self_key: i64) -> i64 {
    let op = node_b(state.1, expr);
    let lhs = node_c(state.1, expr);
    let rhs = node_d(state.1, expr);
    let static_zero = check_static_zero_divisor(state, op, rhs);
    let file = node_file(state.1, expr);
    let start = node_start(state.1, expr);
    let end = node_end(state.1, expr);
    let bool_key = builtin_key_of(state.1, BUILTIN_BOOL);
    let operand_expected = binary_operand_expected(state, op, expected);
    if op == BIN_AND || op == BIN_OR {
        let (l, r) = check_binary_operands(state, (lhs, rhs, operand_expected), ret, impure, self_key);
        if !is_bool_key(state.1, l) {
            push_error(state.3, &format!("logical operator '{}' requires Bool operands", op_text(op)), file, start, end);
        }
        let ok = unify_key(state.1, state.2, state.6, l, r);
        if !ok && key_kind(state.1, l) != TYD_UNKNOWN && key_kind(state.1, r) != TYD_UNKNOWN {
            push_error(state.3, "logical operands have different types", file, start, end);
        }
        expr_set_ty(state.1, expr, bool_key);
        return bool_key;
    }
    if (BIN_EQ..=BIN_GE).contains(&op) {
        let (l, r) = check_binary_operands(state, (lhs, rhs, operand_expected), ret, impure, self_key);
        let ok = unify_key(state.1, state.2, state.6, l, r);
        if !ok {
            if key_kind(state.1, l) != TYD_UNKNOWN && key_kind(state.1, r) != TYD_UNKNOWN {
                push_error(state.3, &format!("comparison '{}' requires operands of the same type", op_text(op)), file, start, end);
            }
        } else if !comparable_key(state.1, l, op) && key_kind(state.1, l) != TYD_UNKNOWN {
            // The operands agree but the type has no comparison. Reported
            // only when they agree, so a mismatch produces one diagnostic
            // rather than a same-type error followed by a not-comparable
            // cascade.
            push_error(state.3, &format!("comparison '{}' is not defined for '{}': compare integer or Bool values, or take the value apart with match", op_text(op), render_key(state.0, state.1, state.2, state.6, state.7, l)), file, start, end);
        }
        expr_set_ty(state.1, expr, bool_key);
        return bool_key;
    }
    let (l, r) = check_binary_operands(state, (lhs, rhs, operand_expected), ret, impure, self_key);
    let lhs_bad = !is_int_key(state.1, l);
    if lhs_bad {
        push_error(state.3, &format!("binary operator '{}' requires integer operands", op_text(op)), file, start, end);
    }
    let ok = unify_key(state.1, state.2, state.6, l, r);
    if lhs_bad {
        // The primary already implicates both operands and the rhs was
        // still checked (its own diagnostics surface); the operands-differ
        // error below would be a cascade, so the expression recovers
        // instead (Single-Fact recovery rule).
        return recover_ty(state, expr, expected);
    }
    if !ok {
        if key_kind(state.1, l) != TYD_UNKNOWN && key_kind(state.1, r) != TYD_UNKNOWN {
            push_error(state.3, &format!("binary operator '{}' requires operands of the same type", op_text(op)), file, start, end);
        }
        return recover_ty(state, expr, expected);
    }
    if op == BIN_DIV || op == BIN_MOD {
        if static_zero == 1 {
            return recover_ty(state, expr, expected);
        }
        let key = division_result_key(state, l);
        expr_set_ty(state.1, expr, key);
        return key;
    }
    expr_set_ty(state.1, expr, l);
    l
}

fn check_array(state: &mut State, expr: i64, expected: i64, ret: i64, impure: i64, self_key: i64) -> i64 {
    let elems = node_b(state.1, expr);
    let count = list_len(state.2, elems);
    let file = node_file(state.1, expr);
    let start = node_start(state.1, expr);
    let end = node_end(state.1, expr);
    if count == 0 {
        if expected != NONE && (key_kind(state.1, expected) == TYD_ARRAY || key_kind(state.1, expected) == TYD_SLICE) {
            expr_set_ty(state.1, expr, expected);
            return expected;
        }
        push_error(state.3, "cannot infer the element type of an empty array", file, start, end);
        return recover_ty(state, expr, expected);
    }
    let elem_expected = if expected != NONE {
        let k = key_kind(state.1, expected);
        if k == TYD_ARRAY || k == TYD_SLICE {
            key_elem(state.1, expected)
        } else {
            NONE
        }
    } else {
        NONE
    };
    // The first element adopts the expected element type (when the array
    // literal is checked against an annotated `[T; N]` or `&[T]` key), so
    // `val bytes: [U8; 4] = [0x0D, 0xF0, 0xAD, 0x0B]` types each literal as
    // U8 and range-checks it against that width; the remaining elements
    // adopt the first element's type as before.
    let first = check_expr(state, list_get(state.2, elems, 0), elem_expected, ret, impure, self_key);
    let mut idx = 1i64;
    while idx < count {
        let key = check_expr(state, list_get(state.2, elems, idx), first, ret, impure, self_key);
        let ok = unify_key(state.1, state.2, state.6, key, first);
        if !ok && key_kind(state.1, key) != TYD_UNKNOWN && key_kind(state.1, first) != TYD_UNKNOWN {
            push_error(state.3, "array elements must have the same type", file, start, end);
        }
        idx += 1;
    }
    let key = canon_tyinfo(state.1, state.2, TYD_ARRAY, NONE, NONE, first, count);
    expr_set_ty(state.1, expr, key);
    key
}

fn key_is_linear_now(state: &mut State, key: i64) -> bool {
    if key == NONE {
        return false;
    }
    let mut seen: Vec<i64> = Vec::new();
    linear_of(state.1, state.2, key, &mut seen) == 1
}

fn index_result_key(state: &mut State, payload: i64) -> i64 {
    let err_sym = state.12;
    if err_sym == NONE {
        return unknown_key(state.1, state.2);
    }
    let err_key = canon_tyinfo(state.1, state.2, TYD_ENUM, err_sym, NONE, NONE, NONE);
    let result_sym = state.9;
    if result_sym == NONE {
        return unknown_key(state.1, state.2);
    }
    let args = alloc_list(state.2);
    list_push(state.2, args, payload);
    list_push(state.2, args, err_key);
    canon_tyinfo(state.1, state.2, TYD_ENUM, result_sym, args, NONE, NONE)
}

fn check_index(state: &mut State, expr: i64, borrow: i64, expected: i64, ret: i64, impure: i64, self_key: i64) -> i64 {
    let base = node_b(state.1, expr);
    let index = node_c(state.1, expr);
    let file = node_file(state.1, expr);
    let start = node_start(state.1, expr);
    let end = node_end(state.1, expr);
    let usize_key = builtin_key_of(state.1, BUILTIN_USIZE);
    let base_key = check_expr(state, base, NONE, ret, impure, self_key);
    let idx_key = check_expr(state, index, usize_key, ret, impure, self_key);
    let idx_ok = unify_key(state.1, state.2, state.6, usize_key, idx_key);
    if !idx_ok && key_kind(state.1, idx_key) != TYD_UNKNOWN {
        push_error(state.3, "array index must be Usize", file, start, end);
    }
    let base_kind = key_kind(state.1, base_key);
    let (elem_key, fixed_len) = if base_kind == TYD_ARRAY {
        (key_elem(state.1, base_key), key_len(state.1, base_key))
    } else if base_kind == TYD_REF || base_kind == TYD_REF_MUT || base_kind == TYD_SLICE {
        let inner = key_elem(state.1, base_key);
        let slice_elem = if key_kind(state.1, inner) == TYD_SLICE {
            key_elem(state.1, inner)
        } else {
            NONE
        };
        if slice_elem == NONE {
            push_error(state.3, "cannot index a value that is not an array or slice", file, start, end);
            return recover_ty(state, expr, expected);
        }
        (slice_elem, NONE)
    } else {
        push_error(state.3, "cannot index a value that is not an array or slice", file, start, end);
        return recover_ty(state, expr, expected);
    };
    if elem_key != NONE && borrow == 0 && key_is_linear_now(state, elem_key) {
        push_error(state.3, "cannot move linear element out of array by index: borrow with & or &mut instead", file, start, end);
    }
    let payload = if borrow == 1 {
        canon_tyinfo(state.1, state.2, TYD_REF, NONE, NONE, elem_key, NONE)
    } else if borrow == 2 {
        canon_tyinfo(state.1, state.2, TYD_REF_MUT, NONE, NONE, elem_key, NONE)
    } else {
        elem_key
    };
    if base_kind == TYD_ARRAY && fixed_len != NONE {
        let (value, ckey) = fold_const(state, index, NONE, 1);
        if key_kind(state.1, ckey) != TYD_UNKNOWN {
            if value < 0 || value >= fixed_len {
                push_error(state.3, &format!("array index out of bounds: index is {} but array length is {}", value, fixed_len), file, start, end);
            }
            expr_set_ty(state.1, expr, payload);
            node_set_d(state.1, expr, INDEX_INFALLIBLE);
            return payload;
        }
    }
    let key = index_result_key(state, payload);
    expr_set_ty(state.1, expr, key);
    node_set_d(state.1, expr, INDEX_FALLIBLE);
    key
}

fn check_field_access(state: &mut State, expr: i64, expected: i64, ret: i64, impure: i64, self_key: i64) -> i64 {
    let base = node_b(state.1, expr);
    let field = node_c(state.1, expr);
    let base_key = check_expr(state, base, NONE, ret, impure, self_key);
    let key = field_access_key(state, expr, base_key, field, expected);
    expr_set_ty(state.1, expr, key);
    key
}

fn check_assign_target(state: &mut State, target: i64, ret: i64, impure: i64, self_key: i64) -> i64 {
    if node_tag(state.1, target) != NODE_EXPR {
        return unknown_key(state.1, state.2);
    }
    let file = node_file(state.1, target);
    let start = node_start(state.1, target);
    let end = node_end(state.1, target);
    let kind = node_a(state.1, target);
    if kind == EXPR_PATH {
        let segs = node_b(state.1, target);
        let count = list_len(state.2, segs);
        let first = list_get(state.2, segs, 0);
        let found = lookup(state.4, first);
        if found.0 == NONE {
            push_error(state.3, &format!("unknown symbol '{}'", name_text(state.0, first)), file, start, end);
            suggest_value_name(state, target, first);
            return recover_ty(state, target, NONE);
        }
        if count == 1 {
            if found.1 == 0 {
                push_error(state.3, &format!("cannot assign to '{}': assignment requires var", name_text(state.0, first)), file, start, end);
                let decl = lookup_full(state.4, first).2;
                if decl != NONE && node_file(state.1, decl) != NO_FILE {
                    push_note_for_last(
                        state.3,
                        state.16,
                        "declared here",
                        node_file(state.1, decl),
                        node_start(state.1, decl),
                        node_end(state.1, decl),
                        NOTE_CONTEXT,
                    );
                }
            }
            expr_set_ty(state.1, target, found.0);
            return found.0;
        }
        check_field_target_base(state, found, first, file, start, end);
        let mut current = found.0;
        let mut idx = 1i64;
        while idx < count {
            let field = list_get(state.2, segs, idx);
            current = field_access_key(state, target, current, field, NONE);
            idx += 1;
        }
        expr_set_ty(state.1, target, current);
        return current;
    }
    if kind == EXPR_FIELD_ACCESS {
        let base = node_b(state.1, target);
        let field = node_c(state.1, target);
        let base_key = check_expr(state, base, NONE, ret, impure, self_key);
        let bkind = key_kind(state.1, base_key);
        if bkind == TYD_REF {
            push_error(state.3, &format!("cannot assign to field '{}' through shared reference '{}': assignment requires &mut", name_text(state.0, field), render_key(state.0, state.1, state.2, state.6, state.7, base_key)), file, start, end);
        } else if bkind == TYD_REF_MUT {

        } else if node_tag(state.1, base) == NODE_EXPR && node_a(state.1, base) == EXPR_PATH {
            let segs = node_b(state.1, base);
            let first = list_get(state.2, segs, 0);
            let found = lookup(state.4, first);
            if found.0 == NONE {
                push_error(state.3, &format!("unknown symbol '{}'", name_text(state.0, first)), file, start, end);
                suggest_value_name(state, base, first);
            } else if found.1 == 0 {
                push_error(state.3, &format!("cannot assign to field '{}' of '{}': assignment requires var", name_text(state.0, field), name_text(state.0, first)), file, start, end);
                let decl = lookup_full(state.4, first).2;
                if decl != NONE && node_file(state.1, decl) != NO_FILE {
                    push_note_for_last(
                        state.3,
                        state.16,
                        "declared here",
                        node_file(state.1, decl),
                        node_start(state.1, decl),
                        node_end(state.1, decl),
                        NOTE_CONTEXT,
                    );
                }
            }
        } else {
            push_error(state.3, &format!("cannot assign to field '{}': the target is not a mutable place", name_text(state.0, field)), file, start, end);
        }
        let key = field_access_key(state, target, base_key, field, NONE);
        expr_set_ty(state.1, target, key);
        return key;
    }
    push_error(state.3, "invalid assignment target", file, start, end);
    recover_ty(state, target, NONE)
}

fn check_field_target_base(state: &mut State, found: (i64, i64), name: i64, file: i64, start: i64, end: i64) {
    let bkind = key_kind(state.1, found.0);
    if bkind == TYD_REF {
        push_error(state.3, &format!("cannot assign to a field through shared reference '{}': assignment requires &mut", render_key(state.0, state.1, state.2, state.6, state.7, found.0)), file, start, end);
    } else if bkind != TYD_REF_MUT && found.1 == 0 {
        push_error(state.3, &format!("cannot assign to field of '{}': assignment requires var", name_text(state.0, name)), file, start, end);
    }
}

fn check_try(state: &mut State, expr: i64, expected: i64, ret: i64, impure: i64, self_key: i64) -> i64 {
    let inner = node_b(state.1, expr);
    let file = node_file(state.1, expr);
    let start = node_start(state.1, expr);
    let end = node_end(state.1, expr);
    let key = check_expr(state, inner, NONE, ret, impure, self_key);
    let result;
    if is_result_key(state.1, key) {
        if !is_result_key(state.1, ret) {
            push_error(state.3, "try on Result requires the enclosing function to return Result", file, start, end);
            result = recover_ty(state, expr, expected);
        } else {
            let args = key_args(state.1, key);
            let ret_args = key_args(state.1, ret);
            let err_key = list_get(state.2, args, 1);
            let ret_err = list_get(state.2, ret_args, 1);
            let err_ok = unify_key(state.1, state.2, state.6, err_key, ret_err);
            if !err_ok && key_kind(state.1, err_key) != TYD_UNKNOWN && key_kind(state.1, ret_err) != TYD_UNKNOWN {
                push_error(state.3, "try error type does not match the function's return type", file, start, end);
            }
            result = list_get(state.2, args, 0);
        }
    } else if is_option_key(state.1, key) {
        if !is_option_key(state.1, ret) {
            push_error(state.3, "try on Option requires the enclosing function to return Option", file, start, end);
            result = recover_ty(state, expr, expected);
        } else {
            let args = key_args(state.1, key);
            result = list_get(state.2, args, 0);
        }
    } else {
        push_error(state.3, "try requires a Result or Option operand", file, start, end);
        result = recover_ty(state, expr, expected);
    }
    expr_set_ty(state.1, expr, result);
    result
}

fn check_path(state: &mut State, expr: i64, expected: i64) -> i64 {
    let sym = expr_sym_of(state.1, expr);
    if sym != NONE {
        return check_path_sym(state, expr, expected, sym);
    }
    check_local_chain(state, expr, expected)
}

fn check_path_sym(state: &mut State, expr: i64, expected: i64, sym: i64) -> i64 {
    let kind = sym_kind(state.1, sym);
    let file = node_file(state.1, expr);
    let start = node_start(state.1, expr);
    let end = node_end(state.1, expr);
    if kind == SYM_CONST {
        let item = sym_decl(state.1, sym);
        let key = ty_key_of(state.1, node_e(state.1, item));
        expr_set_ty(state.1, expr, key);
        return key;
    }
    if kind == SYM_VARIANT {
        return variant_value_key(state, expr, expected, sym);
    }
    if kind == SYM_FUN || kind == SYM_NATIVE_FUN || kind == SYM_TRAIT_METHOD || kind == SYM_IMPL_METHOD {
        push_error(state.3, "function used as a value", file, start, end);
    } else {
        push_error(state.3, "type or module used as a value", file, start, end);
    }
    recover_ty(state, expr, expected)
}

fn variant_value_key(state: &mut State, expr: i64, expected: i64, sym: i64) -> i64 {
    let file = node_file(state.1, expr);
    let start = node_start(state.1, expr);
    let end = node_end(state.1, expr);
    let decl = sym_decl(state.1, sym);
    let key;
    if decl == NONE {
        key = unit_key_of(state);
    } else {
        let enum_sym = enum_sym_of_variant(state.1, sym);
        if enum_sym == NONE {
            push_error(state.3, "cannot find the enum of this variant", file, start, end);
            key = recover_ty(state, expr, expected);
        } else {
            let item = sym_decl(state.1, enum_sym);
            key = enum_key_with_fresh(state.1, state.2, state.6, state.7, expr, enum_sym, item);
            // A payload-bearing variant cannot be used as a bare value: the
            // constructor requires its declared payload values, otherwise
            // codegen would lower an enum with an uninitialised payload.
            let payload_decl = node_b(state.1, decl);
            if list_len(state.2, payload_decl) > 0 {
                push_error(state.3, &format!("variant '{}' requires payload values", name_text(state.0, node_a(state.1, decl))), file, start, end);
            }
        }
    }
    if expected != NONE {
        let ok = unify_key(state.1, state.2, state.6, key, expected);
        if !ok && key_kind(state.1, key) != TYD_UNKNOWN && key_kind(state.1, expected) != TYD_UNKNOWN {
            push_error(state.3, "variant value type mismatch", file, start, end);
        }
    }
    expr_set_ty(state.1, expr, key);
    key
}

fn check_local_chain(state: &mut State, expr: i64, expected: i64) -> i64 {
    let segs = node_b(state.1, expr);
    let count = list_len(state.2, segs);
    let file = node_file(state.1, expr);
    let start = node_start(state.1, expr);
    let end = node_end(state.1, expr);
    let first = list_get(state.2, segs, 0);
    let found = lookup(state.4, first);
    if found.0 == NONE {
        push_error(state.3, &format!("unknown symbol '{}'", name_text(state.0, first)), file, start, end);
        suggest_value_name(state, expr, first);
        return recover_ty(state, expr, expected);
    }
    let mut current = found.0;
    let mut idx = 1i64;
    while idx < count {
        let field = list_get(state.2, segs, idx);
        current = field_access_key(state, expr, current, field, expected);
        idx += 1;
    }
    expr_set_ty(state.1, expr, current);
    current
}

fn field_access_key(state: &mut State, expr: i64, base: i64, field: i64, expected: i64) -> i64 {
    let file = node_file(state.1, expr);
    let start = node_start(state.1, expr);
    let end = node_end(state.1, expr);
    let mut eff = base;
    if key_kind(state.1, eff) == TYD_REF || key_kind(state.1, eff) == TYD_REF_MUT {
        eff = key_elem(state.1, eff);
    }
    if key_kind(state.1, eff) != TYD_STRUCT {
        push_error(state.3, &format!("cannot access field '{}' of a non-struct type", name_text(state.0, field)), file, start, end);
        return recover_ty(state, expr, expected);
    }
    let item = sym_decl(state.1, key_sym(state.1, eff));
    let (found_idx, declared_key) = struct_field_of(state.1, state.2, item, field);
    if found_idx == NONE {
        push_error(state.3, &format!("no field '{}' on type '{}'", name_text(state.0, field), render_key(state.0, state.1, state.2, state.6, state.7, eff)), file, start, end);
        return recover_ty(state, expr, expected);
    }
    // Fields are private to their declaring module unless marked `pub`; the
    // resolver attached the declaring scope to the field row (slot d).
    let fnode = struct_field_node(state.1, state.2, item, field);
    if fnode != NONE && node_c(state.1, fnode) == 0 && node_d(state.1, fnode) != state.13 {
        push_error(state.3, &format!("field '{}' of type '{}' is private to its module", name_text(state.0, field), render_key(state.0, state.1, state.2, state.6, state.7, eff)), file, start, end);
    }
    let from = declared_param_keys(state.1, state.2, item);
    let to = list_to_vec(state.2, key_args(state.1, eff));
    subst_key(state.1, state.2, declared_key, &from, &to)
}

fn struct_field_of(nodes: &[i64], lists: &[Vec<i64>], item: i64, name: i64) -> (i64, i64) {
    let fields = node_e(nodes, item);
    let count = list_len(lists, fields);
    let mut idx = 0i64;
    while idx < count {
        let field = list_get(lists, fields, idx);
        if node_a(nodes, field) == name {
            return (idx, ty_key_of(nodes, node_b(nodes, field)));
        }
        idx += 1;
    }
    (NONE, NONE)
}

fn struct_field_node(nodes: &[i64], lists: &[Vec<i64>], item: i64, name: i64) -> i64 {
    let fields = node_e(nodes, item);
    let count = list_len(lists, fields);
    let mut idx = 0i64;
    while idx < count {
        let field = list_get(lists, fields, idx);
        if node_a(nodes, field) == name {
            return field;
        }
        idx += 1;
    }
    NONE
}

fn enum_sym_of_variant(nodes: &[i64], variant_sym: i64) -> i64 {
    let home = sym_home(nodes, variant_sym);
    let mut idx = 0i64;
    while idx < nodes.len() as i64 / NODE_STRIDE {
        if node_tag(nodes, idx) == NODE_SYM && node_a(nodes, idx) == SYM_ENUM && node_e(nodes, idx) == home {
            return idx;
        }
        idx += 1;
    }
    NONE
}

fn trait_sym_of_method(nodes: &[i64], method_sym: i64) -> i64 {
    let home = sym_home(nodes, method_sym);
    let mut idx = 0i64;
    while idx < nodes.len() as i64 / NODE_STRIDE {
        if node_tag(nodes, idx) == NODE_SYM && node_a(nodes, idx) == SYM_TRAIT && node_e(nodes, idx) == home {
            return idx;
        }
        idx += 1;
    }
    NONE
}

fn enum_key_with_fresh(nodes: &mut Vec<i64>, lists: &mut Vec<Vec<i64>>, vars: &mut Vec<(i64, i64)>, origins: &mut Vec<(i64, i64, i64)>, expr: i64, enum_sym: i64, item: i64) -> i64 {
    let args = fresh_args_for(nodes, lists, vars, origins, expr, item);
    canon_tyinfo(nodes, lists, TYD_ENUM, enum_sym, args, NONE, NONE)
}

fn struct_key_with_fresh(nodes: &mut Vec<i64>, lists: &mut Vec<Vec<i64>>, vars: &mut Vec<(i64, i64)>, origins: &mut Vec<(i64, i64, i64)>, expr: i64, sym: i64, item: i64) -> i64 {
    let args = fresh_args_for(nodes, lists, vars, origins, expr, item);
    canon_tyinfo(nodes, lists, TYD_STRUCT, sym, args, NONE, NONE)
}

fn fresh_args_for(nodes: &mut [i64], lists: &mut Vec<Vec<i64>>, vars: &mut Vec<(i64, i64)>, origins: &mut Vec<(i64, i64, i64)>, expr: i64, item: i64) -> i64 {
    let count = declared_param_count(nodes, lists, item);
    if count == 0 {
        return NONE;
    }
    let args = alloc_list(lists);
    let params = if node_a(nodes, item) == ITEM_NATIVE_TYPE {
        node_e(nodes, item)
    } else {
        node_f(nodes, item)
    };
    let mut idx = 0i64;
    while idx < count {
        let param = list_get(lists, params, idx);
        if node_tag(nodes, param) == NODE_TY && node_a(nodes, param) == TY_PARAM {
            let name = node_b(nodes, param);
            let var = fresh_var(vars, origins, expr, name);
            list_push(lists, args, var);
        }
        idx += 1;
    }
    args
}

fn list_to_vec(lists: &[Vec<i64>], id: i64) -> Vec<i64> {
    let mut out: Vec<i64> = Vec::new();
    let count = list_len(lists, id);
    let mut idx = 0i64;
    while idx < count {
        out.push(list_get(lists, id, idx));
        idx += 1;
    }
    out
}

fn check_call(state: &mut State, expr: i64, expected: i64, ret: i64, impure: i64, self_key: i64) -> i64 {
    let callee = node_b(state.1, expr);
    let file = node_file(state.1, expr);
    let start = node_start(state.1, expr);
    let end = node_end(state.1, expr);
    let result;
    let mut sym = NONE;
    if node_tag(state.1, callee) == NODE_EXPR && node_a(state.1, callee) == EXPR_PATH {
        sym = expr_sym_of(state.1, callee);
        if sym != NONE {
            let kind = sym_kind(state.1, sym);
            if kind == SYM_FUN || kind == SYM_NATIVE_FUN {
                result = check_direct_call(state, expr, expected, sym, ret, impure, self_key);
            } else if kind == SYM_TRAIT_METHOD {
                result = check_trait_call(state, expr, expected, sym, ret, impure, self_key);
            } else if kind == SYM_IMPL_METHOD {
                push_error(state.3, "impl methods cannot be called directly", file, start, end);
                result = recover_ty(state, expr, expected);
            } else {
                push_error(state.3, "cannot call this symbol", file, start, end);
                result = recover_ty(state, expr, expected);
            }
        } else {
            result = check_unresolved_callee(state, expr, expected);
        }
    } else {
        push_error(state.3, "cannot call this expression", file, start, end);
        result = recover_ty(state, expr, expected);
    }
    if expected != NONE {
        let ok = unify_key(state.1, state.2, state.6, result, expected);
        if !ok
            && !key_has_unbound_var(state.1, state.2, state.6, result)
            && key_kind(state.1, result) != TYD_UNKNOWN
            && key_kind(state.1, expected) != TYD_UNKNOWN
        {
            push_error(state.3, &format!("call result type mismatch: expected '{}', found '{}'", render_key(state.0, state.1, state.2, state.6, state.7, expected), render_key(state.0, state.1, state.2, state.6, state.7, result)), file, start, end);
        }
    }
    attach_extraction_binding(state, expr, sym);
    attach_call_tail_safe(state, expr);
    expr_set_ty(state.1, expr, result);
    result
}

// The container binding of an extraction call (NAT_VEC_POP or
// NAT_HASH_MAP_REMOVE), attached to the call's type-argument slot (node_c)
// so the borrow checker reads the binding without re-walking the argument
// list (Single-Fact Rule).  For every other call the slot is cleared to
// NONE: the parser's type-argument list is dead once the call is checked,
// and borrow treats a non-NONE slot as an attached binding.
fn attach_extraction_binding(state: &mut State, expr: i64, sym: i64) {
    let op = if sym != NONE && node_tag(state.1, sym) == NODE_SYM && sym_kind(state.1, sym) == SYM_NATIVE_FUN {
        sym_native_op(state.1, sym)
    } else {
        NAT_NONE
    };
    if op == NAT_VEC_POP || op == NAT_HASH_MAP_REMOVE {
        let first = list_first(state.2, node_d(state.1, expr));
        let mut container_name = NONE;
        if first != NONE && node_tag(state.1, first) == NODE_EXPR {
            let mut cur = first;
            let mut kind = node_a(state.1, cur);
            if kind == EXPR_UNARY {
                let uop = node_b(state.1, cur);
                if uop == UN_REF || uop == UN_REF_MUT {
                    cur = node_c(state.1, cur);
                    kind = node_a(state.1, cur);
                }
            }
            if kind == EXPR_PATH {
                container_name = list_first(state.2, node_b(state.1, cur));
            }
        }
        node_set_c(state.1, expr, container_name);
    } else {
        node_set_c(state.1, expr, NONE);
    }
}

fn check_unresolved_callee(state: &mut State, expr: i64, expected: i64) -> i64 {
    let callee = node_b(state.1, expr);
    let segs = node_b(state.1, callee);
    let count = list_len(state.2, segs);
    let file = node_file(state.1, expr);
    let start = node_start(state.1, expr);
    let end = node_end(state.1, expr);
    if count > 1 {
        let first = list_get(state.2, segs, 0);
        let found = lookup(state.4, first);
        if found.0 == NONE {
            push_error(state.3, &format!("unknown symbol '{}'", name_text(state.0, first)), file, start, end);
            suggest_value_name(state, expr, first);
        } else {
            push_error(state.3, "cannot call a field", file, start, end);
        }
    } else {
        let first = list_get(state.2, segs, 0);
        push_error(state.3, &format!("unknown function '{}'", name_text(state.0, first)), file, start, end);
        suggest_value_name(state, expr, first);
    }
    // The callee could not be resolved and an error was already reported;
    // the call recovers to the expected key (or TYD_UNKNOWN) so the
    // surrounding unification succeeds and no cascading "found '?'"
    // secondary follows the primary diagnostic (Single-Fact recovery rule).
    recover_ty(state, expr, expected)
}

fn check_direct_call(state: &mut State, expr: i64, expected: i64, sym: i64, ret: i64, impure: i64, self_key: i64) -> i64 {
    let decl = sym_decl(state.1, sym);
    if decl == NONE {
        return check_int_from(state, expr, expected, sym, ret, impure, self_key);
    }
    let fn_node = fn_node_of(state.1, decl);
    let kind = sym_kind(state.1, sym);
    // A function not declared `impure` may not call an `impure` function or
    // native (MANIFESTO).  The enclosing purity flag is threaded down from
    // the current function's declaration.
    if node_e(state.1, fn_node) == 1 && impure == 0 {
        push_error(state.3, &format!("impure function '{}' cannot be called from a pure context", name_text(state.0, node_a(state.1, fn_node))), node_file(state.1, expr), node_start(state.1, expr), node_end(state.1, expr));
    }
    let from = fn_declared_param_keys(state.1, state.2, fn_node);
    let (args_list, to) = call_type_args(state, expr, fn_node, &from);
    let params = node_c(state.1, fn_node);
    let arg_exprs = node_d(state.1, expr);
    let pcount = list_len(state.2, params);
    let acount = list_len(state.2, arg_exprs);
    if pcount != acount {
        push_error(state.3, &format!("function '{}' expects {} arguments, found {}", name_text(state.0, node_a(state.1, fn_node)), pcount, acount), node_file(state.1, expr), node_start(state.1, expr), node_end(state.1, expr));
    }
    let param_keys = alloc_list(state.2);
    let mut inferred_ok = true;
    let mut idx = 0i64;
    while idx < pcount {
        let param = list_get(state.2, params, idx);
        let declared = ty_key_of(state.1, node_b(state.1, param));
        let concrete = subst_key(state.1, state.2, declared, &from, &to);
        list_push(state.2, param_keys, concrete);
        let arg = list_get(state.2, arg_exprs, idx);
        if arg == NONE {
            // The arity mismatch was already reported; the missing argument
            // has no node to check, so the loop stops here (no "argument N
            // has type '?'" cascade).
            break;
        }
        let akey = check_expr(state, arg, concrete, ret, impure, self_key);
        let ok = unify_key(state.1, state.2, state.6, akey, concrete);
        if !ok {
            inferred_ok = false;
            if !key_has_unbound_var(state.1, state.2, state.6, concrete)
                && key_kind(state.1, concrete) != TYD_UNKNOWN
                && key_kind(state.1, akey) != TYD_UNKNOWN
            {
                push_error(state.3, &format!("argument {} of '{}' has type '{}', expected '{}'", idx + 1, name_text(state.0, node_a(state.1, fn_node)), render_key(state.0, state.1, state.2, state.6, state.7, akey), render_key(state.0, state.1, state.2, state.6, state.7, concrete)), node_file(state.1, arg), node_start(state.1, arg), node_end(state.1, arg));
            }
        }
        idx += 1;
    }
    if kind == SYM_NATIVE_FUN {
        let op = sym_native_op(state.1, sym);
        if op == NAT_VEC_PUSH || op == NAT_HASH_MAP_INSERT {
            check_container_resolvability(state, expr, param_keys);
        }
    }
    if !inferred_ok {
        let mut t_idx = 0i64;
        while t_idx < to.len() as i64 {
            let targ = list_get(state.2, args_list, t_idx);
            if key_has_unbound_var(state.1, state.2, state.6, targ) {
                let name = var_origin_name(state.7, targ);
                let tname = if name == NONE { String::from("?") } else { name_text(state.0, name) };
                let fname = name_text(state.0, node_a(state.1, fn_node));
                push_error(state.3, &format!("cannot infer type parameter '{}' for '{}': specify type arguments explicitly (e.g. {}[U8](...))", tname, fname, fname), node_file(state.1, expr), node_start(state.1, expr), node_end(state.1, expr));
                break;
            }
            t_idx += 1;
        }
    }
    let declared_ret = ty_key_of(state.1, node_d(state.1, fn_node));
    let result = subst_key(state.1, state.2, declared_ret, &from, &to);
    let mono_slot = if kind == SYM_NATIVE_FUN { sym } else { fn_node };
    let mono = canon_tyinfo(state.1, state.2, TYD_MONO, mono_slot, args_list, NONE, NONE);
    let inst = instance_of(
        state.1,
        (node_file(state.1, expr), node_start(state.1, expr), node_end(state.1, expr)),
        (mono, mono_slot, args_list, result, param_keys, kind),
    );
    expr_set_sym(state.1, expr, inst);
    result
}

// The Resolvability Rule (MANIFESTO): a native container type C(T) may hold
// linear elements only if its native surface provides a by-value extraction
// function.  At every insertion call (vec_push, hash_map_insert) the element
// key is the container's last type argument; if it is linear, the container's
// type symbol must carry the extraction flag the resolver attached.
fn check_container_resolvability(state: &mut State, expr: i64, param_keys: i64) {
    let count = list_len(state.2, param_keys);
    let mut idx = 0i64;
    while idx < count {
        let key = deref_key(state.1, list_get(state.2, param_keys, idx));
        if key_kind(state.1, key) == TYD_NATIVE {
            let args = key_args(state.1, key);
            if args != NONE {
                // Any linear type argument is a linear obligation living
                // inside the container: for HashMap(K, V) both the key and
                // the value count, not just the value.
                let acount = list_len(state.2, args);
                let mut ai = 0i64;
                let mut has_linear = 0;
                let mut seen: Vec<i64> = Vec::new();
                while ai < acount {
                    if linear_of(state.1, state.2, list_get(state.2, args, ai), &mut seen) == 1 {
                        has_linear = 1;
                    }
                    ai += 1;
                }
                if has_linear == 1 {
                    let cty_sym = key_sym_of(state.1, key);
                    if cty_sym == NONE || node_f(state.1, cty_sym) == NONE {
                        push_error(
                            state.3,
                            "cannot store linear element in container: its native API provides no by-value extraction operation",
                            node_file(state.1, expr),
                            node_start(state.1, expr),
                            node_end(state.1, expr),
                        );
                        return;
                    }
                }
            }
        }
        idx += 1;
    }
}

fn key_sym_of(nodes: &[i64], key: i64) -> i64 {
    let row = find_tyinfo(nodes, key);
    if row == NONE {
        NONE
    } else {
        node_c(nodes, row)
    }
}

fn instance_of(
    nodes: &mut Vec<i64>,
    span: (i64, i64, i64),
    data: (i64, i64, i64, i64, i64, i64),
) -> i64 {
    let mono = data.0;
    let existing = find_instance(nodes, mono);
    if existing != NONE {
        return existing;
    }
    alloc_instance(
        nodes,
        span,
        (data.1, data.2, data.3, data.4, data.0, data.5),
    )
}

fn fn_node_of(nodes: &[i64], decl: i64) -> i64 {
    if node_tag(nodes, decl) == NODE_FN {
        decl
    } else {
        node_d(nodes, decl)
    }
}

fn fn_declared_param_keys(nodes: &mut Vec<i64>, lists: &mut [Vec<i64>], fn_node: i64) -> Vec<i64> {
    let tparams = node_b(nodes, fn_node);
    let count = list_len(lists, tparams);
    let mut keys: Vec<i64> = Vec::new();
    let mut idx = 0i64;
    while idx < count {
        let param = list_get(lists, tparams, idx);
        if node_tag(nodes, param) == NODE_TY && node_a(nodes, param) == TY_PARAM {
            let name = node_b(nodes, param);
            let bound = node_c(nodes, param);
            keys.push(param_decl_key(nodes, lists, fn_node, name, bound));
        }
        idx += 1;
    }
    keys
}

fn call_type_args(state: &mut State, expr: i64, fn_node: i64, from: &[i64]) -> (i64, Vec<i64>) {
    let tcount = from.len() as i64;
    if tcount == 0 {
        return (NONE, Vec::new());
    }
    let targs_expr = node_c(state.1, expr);
    let file = node_file(state.1, expr);
    let start = node_start(state.1, expr);
    let end = node_end(state.1, expr);
    let args = alloc_list(state.2);
    if targs_expr != NONE {
        let explicit = canon_ty_list(state, targs_expr, NONE, 1);
        let ec = list_len(state.2, explicit);
        if ec != tcount {
            push_error(state.3, &format!("type arguments: expected {}, found {}", tcount, ec), file, start, end);
        }
        let mut idx = 0i64;
        while idx < ec && idx < tcount {
            let item = list_get(state.2, explicit, idx);
            list_push(state.2, args, item);
            idx += 1;
        }
    } else {
        let tparams = node_b(state.1, fn_node);
        let mut idx = 0i64;
        while idx < tcount {
            let param = list_get(state.2, tparams, idx);
            let name = if node_tag(state.1, param) == NODE_TY {
                node_b(state.1, param)
            } else {
                NONE
            };
            let var = fresh_var(state.6, state.7, expr, name);
            list_push(state.2, args, var);
            idx += 1;
        }
    }
    let to = list_to_vec(state.2, args);
    (args, to)
}

fn check_int_from(state: &mut State, expr: i64, expected: i64, sym: i64, ret: i64, impure: i64, self_key: i64) -> i64 {
    let home = sym_home(state.1, sym);
    let receiver_sym = builtin_type_of_scope(state.1, home);
    let file = node_file(state.1, expr);
    let start = node_start(state.1, expr);
    let end = node_end(state.1, expr);
    if receiver_sym == NONE {
        push_error(state.3, "cannot resolve the receiver type of 'from'", file, start, end);
        return recover_ty(state, expr, expected);
    }
    let receiver_key = builtin_key_of_sym(state.1, receiver_sym);
    if !is_int_key(state.1, receiver_key) {
        push_error(state.3, &format!("'from' is only defined for integer types, not '{}'", render_key(state.0, state.1, state.2, state.6, state.7, receiver_key)), file, start, end);
        return recover_ty(state, expr, expected);
    }
    let arg_exprs = node_d(state.1, expr);
    let acount = list_len(state.2, arg_exprs);
    if acount != 1 {
        push_error(state.3, "'from' expects exactly one argument", file, start, end);
    }
    // The conversion accepts any integer scalar; codegen selects the LLVM
    // cast from the source and destination width/signedness metadata.
    let arg = list_get(state.2, arg_exprs, 0);
    let akey = check_expr(state, arg, NONE, ret, impure, self_key);
    if !is_int_key(state.1, akey) {
        push_error(state.3, &format!("'from' argument must be an integer, found '{}'", render_key(state.0, state.1, state.2, state.6, state.7, akey)), node_file(state.1, arg), node_start(state.1, arg), node_end(state.1, arg));
    }
    let args_list = alloc_list(state.2);
    list_push(state.2, args_list, receiver_key);
    list_push(state.2, args_list, akey);
    // The mono key carries both the receiver and the source type: codegen
    // keys the lowered conversion function by this mono key, so without the
    // source type every `I64.from(...)` call would share the first-seen
    // parameter layout and call an i8-parameter function with i16/i32/i64
    // arguments.
    let mono = canon_tyinfo(state.1, state.2, TYD_MONO, sym, args_list, NONE, NONE);
    let param_keys = alloc_list(state.2);
    list_push(state.2, param_keys, akey);
    let inst = instance_of(
        state.1,
        (file, start, end),
        (mono, sym, args_list, receiver_key, param_keys, SYM_NATIVE_FUN),
    );
    expr_set_sym(state.1, expr, inst);
    receiver_key
}

fn builtin_type_of_scope(nodes: &[i64], scope: i64) -> i64 {
    let mut idx = 0i64;
    while idx < nodes.len() as i64 / NODE_STRIDE {
        if node_tag(nodes, idx) == NODE_SYM && node_a(nodes, idx) == SYM_TYPE && node_e(nodes, idx) == scope {
            return idx;
        }
        idx += 1;
    }
    NONE
}

fn check_trait_call(state: &mut State, expr: i64, expected: i64, sym: i64, ret: i64, impure: i64, self_key: i64) -> i64 {
    let trait_sym = trait_sym_of_method(state.1, sym);
    let file = node_file(state.1, expr);
    let start = node_start(state.1, expr);
    let end = node_end(state.1, expr);
    if trait_sym == NONE {
        push_error(state.3, "cannot find the trait of this method", file, start, end);
        return recover_ty(state, expr, expected);
    }
    let trait_item = sym_decl(state.1, trait_sym);
    let method_name = node_a(state.1, sym_decl(state.1, sym));
    let trait_method = find_method_by_name(state.1, state.2, node_e(state.1, trait_item), method_name);
    if trait_method == NONE {
        push_error(state.3, "trait method not found", file, start, end);
        return recover_ty(state, expr, expected);
    }
    let arg_exprs = node_d(state.1, expr);
    let acount = list_len(state.2, arg_exprs);
    if acount == 0 {
        push_error(state.3, "trait method call requires a receiver argument", file, start, end);
    }
    let receiver = list_get(state.2, arg_exprs, 0);
    let rkey = check_expr(state, receiver, NONE, ret, impure, self_key);
    let recv = deref_key(state.1, rkey);
    let result = if key_kind(state.1, recv) == TYD_PARAM {
        trait_call_deferred(state, expr, trait_sym, trait_method, recv, arg_exprs, (ret, impure, self_key))
    } else {
        trait_call_concrete(state, expr, trait_sym, trait_method, recv, arg_exprs, (ret, impure, self_key, expected))
    };
    expr_set_ty(state.1, expr, result);
    result
}

fn trait_call_concrete(state: &mut State, expr: i64, trait_sym: i64, trait_method: i64, recv: i64, arg_exprs: i64, fctx: (i64, i64, i64, i64)) -> i64 {
    let (ret, impure, self_key, expected) = fctx;
    let file = node_file(state.1, expr);
    let start = node_start(state.1, expr);
    let end = node_end(state.1, expr);
    let impl_idx = impl_find(state.5, trait_sym, recv);
    if impl_idx == NONE {
        push_error(state.3, &format!("type '{}' does not implement trait '{}'", render_key(state.0, state.1, state.2, state.6, state.7, recv), name_text(state.0, sym_name(state.1, trait_sym))), file, start, end);
        return recover_ty(state, expr, expected);
    }
    let methods = impl_methods(state.5, impl_idx);
    let method_name = node_a(state.1, trait_method);
    let method = find_method_by_name(state.1, state.2, methods, method_name);
    if method == NONE {
        push_error(state.3, "impl method not found", file, start, end);
        return recover_ty(state, expr, expected);
    }
    if node_e(state.1, method) == 1 && impure == 0 {
        push_error(state.3, &format!("impure trait method '{}' cannot be called from a pure context", name_text(state.0, node_a(state.1, method))), file, start, end);
    }
    let fn_node = method;
    let params = node_c(state.1, fn_node);
    let pcount = list_len(state.2, params);
    let param_keys = alloc_list(state.2);
    let mut idx = 0i64;
    while idx < pcount {
        let param = list_get(state.2, params, idx);
        let key = ty_key_of(state.1, node_b(state.1, param));
        list_push(state.2, param_keys, key);
        let arg = list_get(state.2, arg_exprs, idx);
        let akey = check_expr(state, arg, key, ret, impure, self_key);
        let ok = unify_key(state.1, state.2, state.6, akey, key);
        if !ok && key_kind(state.1, akey) != TYD_UNKNOWN && key_kind(state.1, key) != TYD_UNKNOWN {
            push_error(state.3, &format!("argument {} has type '{}', expected '{}'", idx + 1, render_key(state.0, state.1, state.2, state.6, state.7, akey), render_key(state.0, state.1, state.2, state.6, state.7, key)), node_file(state.1, arg), node_start(state.1, arg), node_end(state.1, arg));
        }
        idx += 1;
    }
    let result = ty_key_of(state.1, node_d(state.1, fn_node));
    let mono = canon_tyinfo(state.1, state.2, TYD_MONO, fn_node, NONE, NONE, NONE);
    let inst = instance_of(
        state.1,
        (file, start, end),
        (mono, fn_node, NONE, result, param_keys, SYM_IMPL_METHOD),
    );
    alloc_trait_call(state.1, expr, inst, trait_sym, method_name, trait_method);
    expr_set_sym(state.1, expr, inst);
    result
}

fn trait_call_deferred(state: &mut State, expr: i64, trait_sym: i64, trait_method: i64, recv: i64, arg_exprs: i64, fctx: (i64, i64, i64)) -> i64 {
    let (ret, impure, self_key) = fctx;
    let file = node_file(state.1, expr);
    let start = node_start(state.1, expr);
    let end = node_end(state.1, expr);
    if !param_has_bound(state.1, recv, trait_sym) {
        push_error(state.3, &format!("type parameter '{}' does not implement trait '{}'", name_text(state.0, key_sym(state.1, recv)), name_text(state.0, sym_name(state.1, trait_sym))), file, start, end);
    }
    // A trait method not declared `impure` may not be called from a pure
    // context (MANIFESTO); the enclosing purity flag is threaded down.
    if node_e(state.1, trait_method) == 1 && impure == 0 {
        push_error(state.3, &format!("impure trait method '{}' cannot be called from a pure context", name_text(state.0, node_a(state.1, trait_method))), file, start, end);
    }
    push_scope(state.4);
    let tparams = node_b(state.1, trait_method);
    bind_type_params(state.1, state.2, state.4, trait_method, tparams);
    let params = node_c(state.1, trait_method);
    let pcount = list_len(state.2, params);
    let mut idx = 0i64;
    while idx < pcount {
        let param = list_get(state.2, params, idx);
        let param_ty = node_b(state.1, param);
        let key = canon_ty(state, param_ty, recv, 0);
        let arg = list_get(state.2, arg_exprs, idx);
        let akey = check_expr(state, arg, key, ret, impure, self_key);
        let ok = unify_key(state.1, state.2, state.6, akey, key);
        if !ok && key_kind(state.1, akey) != TYD_UNKNOWN && key_kind(state.1, key) != TYD_UNKNOWN {
            push_error(state.3, &format!("argument {} has type '{}', expected '{}'", idx + 1, render_key(state.0, state.1, state.2, state.6, state.7, akey), render_key(state.0, state.1, state.2, state.6, state.7, key)), node_file(state.1, arg), node_start(state.1, arg), node_end(state.1, arg));
        }
        idx += 1;
    }
    let ret_ty = node_d(state.1, trait_method);
    let result = canon_ty(state, ret_ty, recv, 0);
    pop_scope(state.4);
    let method_name = node_a(state.1, trait_method);
    alloc_trait_call(state.1, expr, NONE, trait_sym, method_name, trait_method);
    result
}

fn param_has_bound(nodes: &[i64], key: i64, trait_sym: i64) -> bool {
    if key_kind(nodes, key) != TYD_PARAM {
        return false;
    }
    let row = find_tyinfo(nodes, key);
    if row == NONE {
        return false;
    }
    node_f(nodes, row) == trait_sym
}

fn deref_key(nodes: &[i64], key: i64) -> i64 {
    let kind = key_kind(nodes, key);
    if kind == TYD_REF || kind == TYD_REF_MUT {
        key_elem(nodes, key)
    } else {
        key
    }
}

fn check_struct_lit(state: &mut State, expr: i64, expected: i64, ret: i64, impure: i64, self_key: i64) -> i64 {
    let sym = expr_sym_of(state.1, expr);
    let file = node_file(state.1, expr);
    let start = node_start(state.1, expr);
    let end = node_end(state.1, expr);
    let result;
    if sym == NONE {
        push_error(state.3, "cannot resolve the type of this literal", file, start, end);
        result = recover_ty(state, expr, expected);
    } else {
        let kind = sym_kind(state.1, sym);
        if kind == SYM_STRUCT {
            result = check_struct_construct(state, expr, sym, ret, impure, self_key);
        } else if kind == SYM_VARIANT {
            result = check_variant_construct(state, expr, expected, sym, ret, impure, self_key);
        } else {
            push_error(state.3, "cannot construct a value of this symbol", file, start, end);
            result = recover_ty(state, expr, expected);
        }
    }
    if expected != NONE {
        let ok = unify_key(state.1, state.2, state.6, result, expected);
        if !ok && key_kind(state.1, result) != TYD_UNKNOWN && key_kind(state.1, expected) != TYD_UNKNOWN {
            push_error(state.3, &format!("constructed value type mismatch: expected '{}', found '{}'", render_key(state.0, state.1, state.2, state.6, state.7, expected), render_key(state.0, state.1, state.2, state.6, state.7, result)), file, start, end);
        }
    }
    expr_set_ty(state.1, expr, result);
    result
}

fn check_struct_construct(state: &mut State, expr: i64, sym: i64, ret: i64, impure: i64, self_key: i64) -> i64 {
    let file = node_file(state.1, expr);
    let start = node_start(state.1, expr);
    let end = node_end(state.1, expr);
    let item = sym_decl(state.1, sym);
    let key = struct_key_with_fresh(state.1, state.2, state.6, state.7, expr, sym, item);
    let args = key_args(state.1, key);
    let from = declared_param_keys(state.1, state.2, item);
    let to = list_to_vec(state.2, args);
    let field_names = node_c(state.1, expr);
    let values = node_d(state.1, expr);
    let fcount = list_len(state.2, field_names);
    let vcount = list_len(state.2, values);
    if fcount != vcount {
        push_error(state.3, "struct literal field/value count mismatch", file, start, end);
    }
    let mut idx = 0i64;
    while idx < fcount {
        let name = list_get(state.2, field_names, idx);
        let (found_idx, declared) = struct_field_of(state.1, state.2, item, name);
        if found_idx == NONE {
            push_error(state.3, &format!("no field '{}' on struct '{}'", name_text(state.0, name), name_text(state.0, sym_name(state.1, sym))), file, start, end);
        } else {
            let concrete = subst_key(state.1, state.2, declared, &from, &to);
            let value = list_get(state.2, values, idx);
            if value == NONE {
                // The count mismatch was already reported; the missing value
                // has no node to check.
                break;
            }
            let vkey = check_expr(state, value, concrete, ret, impure, self_key);
            let ok = unify_key(state.1, state.2, state.6, vkey, concrete);
            if !ok && key_kind(state.1, vkey) != TYD_UNKNOWN && key_kind(state.1, concrete) != TYD_UNKNOWN {
                push_error(state.3, &format!("field '{}' has type '{}', expected '{}'", name_text(state.0, name), render_key(state.0, state.1, state.2, state.6, state.7, vkey), render_key(state.0, state.1, state.2, state.6, state.7, concrete)), node_file(state.1, value), node_start(state.1, value), node_end(state.1, value));
            }
        }
        idx += 1;
    }
    // A struct literal must initialize every declared field; an absent field
    // would be left uninitialised in the lowered value.
    if item != NONE && node_tag(state.1, item) == NODE_ITEM {
        let declared_fields = node_e(state.1, item);
        let dcount = list_len(state.2, declared_fields);
        let mut didx = 0i64;
        while didx < dcount {
            let df = list_get(state.2, declared_fields, didx);
            let dname = node_a(state.1, df);
            let mut present = 0;
            let mut pidx = 0i64;
            while pidx < fcount {
                if list_get(state.2, field_names, pidx) == dname {
                    present = 1;
                    break;
                }
                pidx += 1;
            }
            if present == 0 {
                push_error(state.3, &format!("struct literal is missing field '{}'", name_text(state.0, dname)), file, start, end);
            }
            didx += 1;
        }
    }
    key
}

fn check_variant_construct(state: &mut State, expr: i64, expected: i64, sym: i64, ret: i64, impure: i64, self_key: i64) -> i64 {
    let file = node_file(state.1, expr);
    let start = node_start(state.1, expr);
    let end = node_end(state.1, expr);
    let decl = sym_decl(state.1, sym);
    if decl == NONE {
        let key = unit_key_of(state);
        return key;
    }
    let enum_sym = enum_sym_of_variant(state.1, sym);
    if enum_sym == NONE {
        push_error(state.3, "cannot find the enum of this variant", file, start, end);
        return recover_ty(state, expr, expected);
    }
    let enum_item = sym_decl(state.1, enum_sym);
    let key = enum_key_with_fresh(state.1, state.2, state.6, state.7, expr, enum_sym, enum_item);
    let args = key_args(state.1, key);
    let from = declared_param_keys(state.1, state.2, enum_item);
    let to = list_to_vec(state.2, args);
    let payload_decl = node_b(state.1, decl);
    let pcount = list_len(state.2, payload_decl);
    let values = node_d(state.1, expr);
    let vcount = list_len(state.2, values);
    if pcount != vcount {
        push_error(state.3, &format!("variant '{}' expects {} payload values, found {}", name_text(state.0, node_a(state.1, decl)), pcount, vcount), file, start, end);
    }
    let mut idx = 0i64;
    while idx < pcount {
        let declared = ty_key_of(state.1, list_get(state.2, payload_decl, idx));
        let concrete = subst_key(state.1, state.2, declared, &from, &to);
        let value = list_get(state.2, values, idx);
        if value == NONE {
            // The arity mismatch was already reported; the missing payload
            // has no node to check.
            break;
        }
        let vkey = check_expr(state, value, concrete, ret, impure, self_key);
        let ok = unify_key(state.1, state.2, state.6, vkey, concrete);
        if !ok && key_kind(state.1, vkey) != TYD_UNKNOWN && key_kind(state.1, concrete) != TYD_UNKNOWN {
            push_error(state.3, &format!("payload {} of '{}' has type '{}', expected '{}'", idx + 1, name_text(state.0, node_a(state.1, decl)), render_key(state.0, state.1, state.2, state.6, state.7, vkey), render_key(state.0, state.1, state.2, state.6, state.7, concrete)), node_file(state.1, value), node_start(state.1, value), node_end(state.1, value));
        }
        idx += 1;
    }
    key
}

fn check_match(state: &mut State, expr: i64, expected: i64, ret: i64, impure: i64, self_key: i64) -> i64 {
    let scrutinee = node_b(state.1, expr);
    let arms = node_c(state.1, expr);
    let file = node_file(state.1, expr);
    let start = node_start(state.1, expr);
    let end = node_end(state.1, expr);
    let s_key = check_expr(state, scrutinee, NONE, ret, impure, self_key);
    let count = list_len(state.2, arms);
    let mut merged = NONE;
    let mut arms_ok = true;
    let mut first = true;
    let mut idx = 0i64;
    while idx < count {
        let arm = list_get(state.2, arms, idx);
        let arm_key = check_arm(state, arm, (s_key, scrutinee), ret, impure, self_key, merged);
        let div = stmt_diverges(state.1, state.2, node_b(state.1, arm));
        if div == 0 {
            if first {
                merged = arm_key;
                first = false;
            } else {
                let ok = unify_key(state.1, state.2, state.6, merged, arm_key);
                if !ok {
                    arms_ok = false;
                    if key_kind(state.1, merged) != TYD_UNKNOWN && key_kind(state.1, arm_key) != TYD_UNKNOWN {
                        push_error(state.3, &format!("match arms have different types: '{}' and '{}'", render_key(state.0, state.1, state.2, state.6, state.7, merged), render_key(state.0, state.1, state.2, state.6, state.7, arm_key)), node_file(state.1, arm), node_start(state.1, arm), node_end(state.1, arm));
                    }
                }
            }
        }
        idx += 1;
    }
    if merged == NONE {
        merged = unit_key_of(state);
    }
    check_exhaustive(state, s_key, arms, file, start, end);
    if !arms_ok {
        // The arms-mismatch primary was already emitted; the match recovers
        // so no "cannot assign '...' to '...'" cascade follows it.
        return recover_ty(state, expr, expected);
    }
    expr_set_ty(state.1, expr, merged);
    merged
}

fn check_arm(state: &mut State, arm: i64, scrut: (i64, i64), ret: i64, impure: i64, self_key: i64, expected: i64) -> i64 {
    push_scope(state.4);
    check_pattern(state, node_a(state.1, arm), scrut.0, scrut.1);
    attach_local_facts(state, arm);
    let body = node_b(state.1, arm);
    let key = if node_tag(state.1, body) == NODE_STMT && node_a(state.1, body) == STMT_EXPR {
        // Later arms are checked against the merged type of the non-diverging
        // arms seen so far, so an arm literal adopts it (`Err(DivByZero) => 0`
        // against a U8 `Ok` arm) instead of defaulting to I64 and failing to
        // unify.  The first non-diverging arm is still checked with no
        // expected type, exactly as before.
        check_expr(state, node_b(state.1, body), expected, ret, impure, self_key)
    } else {
        check_stmt(state, body, ret, impure, self_key)
    };
    pop_scope(state.4);
    key
}

fn check_pattern(state: &mut State, pat: i64, s_key: i64, scrutinee: i64) -> i64 {
    if node_tag(state.1, pat) != NODE_PAT {
        return unknown_key(state.1, state.2);
    }
    let kind = node_a(state.1, pat);
    let file = node_file(state.1, pat);
    let start = node_start(state.1, pat);
    let end = node_end(state.1, pat);
    if kind == PAT_BIND {
        let name = node_b(state.1, pat);
        // The bound value is (a subpart of) the match scrutinee, so its
        // frame-rootedness is the scrutinee's; the tail-safety trace reads
        // this fact back without re-walking the arm list.
        alloc_patfact(state.1, pat, scrutinee);
        bind(state.4, name, s_key, 0, pat);
        pat_set_ty(state.1, pat, s_key);
        return s_key;
    }
    if kind == PAT_LIT {
        let lit = node_b(state.1, pat);
        let is_bool = lit == LIT_TRUE || lit == LIT_FALSE;
        let mut key = if is_bool {
            builtin_key_of(state.1, BUILTIN_BOOL)
        } else {
            builtin_key_of(state.1, BUILTIN_I64)
        };
        // A literal pattern carries the scrutinee's own scalar type when that
        // type is a primitive integer or Bool, so `5` matches a U8 scrutinee
        // instead of forcing an I64 key that cannot unify.
        let scrut = deref_key(state.1, s_key);
        if key_kind(state.1, scrut) == TYD_BUILTIN {
            let sub = tyinfo_builtin_kind(state.1, scrut);
            let matches = if is_bool {
                sub == BUILTIN_BOOL
            } else {
                builtin_int_is_int(sub)
            };
            if matches {
                key = scrut;
            }
        }
        if !is_bool && key_kind(state.1, key) == TYD_BUILTIN {
            range_check_literal(state, node_c(state.1, pat), node_b(state.1, pat), 0, key, (file, start, end), 0);
        }
        let ok = unify_key(state.1, state.2, state.6, key, s_key);
        if !ok {
            push_error(state.3, &format!("literal pattern type mismatch: expected '{}'", render_key(state.0, state.1, state.2, state.6, state.7, s_key)), file, start, end);
        }
        pat_set_ty(state.1, pat, key);
        return key;
    }
    if kind == PAT_PATH || kind == PAT_VARIANT {
        let sym = pat_sym_of(state.1, pat);
        if sym == NONE {
            push_error(state.3, "cannot resolve pattern", file, start, end);
            return recover_ty(state, pat, NONE);
        }
        if !variant_matches(state.1, s_key, sym) {
            push_error(state.3, "this pattern does not match the scrutinee type", file, start, end);
        }
        if kind == PAT_VARIANT {
            let decl = sym_decl(state.1, sym);
            let payload_decl = node_b(state.1, decl);
            let pcount = list_len(state.2, payload_decl);
            let args = key_args(state.1, s_key);
            let enum_sym = enum_sym_of_variant(state.1, sym);
            let enum_item = sym_decl(state.1, enum_sym);
            let from = declared_param_keys(state.1, state.2, enum_item);
            let to = list_to_vec(state.2, args);
            let payload_pats = node_c(state.1, pat);
            let pc = list_len(state.2, payload_pats);
            if pcount != pc {
                push_error(state.3, &format!("variant pattern '{}' expects {} payload patterns, found {}", name_text(state.0, node_a(state.1, decl)), pcount, pc), file, start, end);
            }
            let mut idx = 0i64;
            while idx < pcount {
                let declared = ty_key_of(state.1, list_get(state.2, payload_decl, idx));
                let concrete = subst_key(state.1, state.2, declared, &from, &to);
                check_pattern(state, list_get(state.2, payload_pats, idx), concrete, scrutinee);
                idx += 1;
            }
        }
        pat_set_ty(state.1, pat, s_key);
        return s_key;
    }
    let inner = deref_key(state.1, s_key);
    let inner_kind = key_kind(state.1, inner);
    if inner_kind != TYD_SLICE && inner_kind != TYD_ARRAY {
        push_error(state.3, "array pattern requires a slice or array scrutinee", file, start, end);
        return recover_ty(state, pat, NONE);
    }
    let elem = key_elem(state.1, inner);
    let elems = node_b(state.1, pat);
    let ecount = list_len(state.2, elems);
    let mut idx = 0i64;
    while idx < ecount {
        check_pattern(state, list_get(state.2, elems, idx), elem, scrutinee);
        idx += 1;
    }
    let rest = node_c(state.1, pat);
    if rest != NONE {
        let rest_key = rest_type_of(state.1, state.2, s_key, inner);
        // A rest binding is a slice view of the scrutinee, so its
        // frame-rootedness is the scrutinee's; the tail-safety trace reads
        // this fact back without re-walking the arm list.
        alloc_patfact(state.1, pat, scrutinee);
        bind(state.4, rest, rest_key, 0, pat);
        pat_set_rest_key(state.1, pat, rest_key);
    }
    pat_set_ty(state.1, pat, s_key);
    s_key
}

fn rest_type_of(nodes: &mut Vec<i64>, lists: &mut [Vec<i64>], s_key: i64, inner: i64) -> i64 {
    let is_mut = key_kind(nodes, s_key) == TYD_REF_MUT;
    let rest = canon_tyinfo(nodes, lists, TYD_SLICE, NONE, NONE, key_elem(nodes, inner), NONE);
    let kind_of = if is_mut { TYD_REF_MUT } else { TYD_REF };
    canon_tyinfo(nodes, lists, kind_of, NONE, NONE, rest, NONE)
}

fn variant_matches(nodes: &[i64], s_key: i64, variant_sym: i64) -> bool {
    let s_kind = key_kind(nodes, s_key);
    if s_kind == TYD_BUILTIN {
        return sym_decl(nodes, variant_sym) == NONE;
    }
    if s_kind != TYD_ENUM {
        return false;
    }
    let enum_sym = key_sym(nodes, s_key);
    node_e(nodes, enum_sym) == sym_home(nodes, variant_sym)
}

fn check_exhaustive(state: &mut State, s_key: i64, arms: i64, file: i64, start: i64, end: i64) {
    let count = list_len(state.2, arms);
    let mut has_bind = false;
    let mut idx = 0i64;
    while idx < count {
        let pat = node_a(state.1, list_get(state.2, arms, idx));
        if node_tag(state.1, pat) == NODE_PAT && node_a(state.1, pat) == PAT_BIND {
            has_bind = true;
        }
        idx += 1;
    }
    if has_bind {
        return;
    }
    let inner = deref_key(state.1, s_key);
    let kind = key_kind(state.1, inner);
    if kind == TYD_ENUM {
        let enum_sym = key_sym(state.1, inner);
        let item = sym_decl(state.1, enum_sym);
        let variants = node_e(state.1, item);
        let vcount = list_len(state.2, variants);
        let mut v_idx = 0i64;
        while v_idx < vcount {
            let variant = list_get(state.2, variants, v_idx);
            if !variant_covered(state.1, state.2, arms, variant) {
                push_error(state.3, &format!("non-exhaustive match: missing variant '{}'", name_text(state.0, node_a(state.1, variant))), file, start, end);
            }
            v_idx += 1;
        }
    } else if kind == TYD_ARRAY {
        let n = key_len(state.1, inner);
        if !array_covers_len(state.1, state.2, arms, n) {
            push_error(state.3, "non-exhaustive match: no arm covers this array length", file, start, end);
        }
    } else if kind == TYD_SLICE {
        if !slice_exhaustive(state.1, state.2, arms) {
            push_error(state.3, "non-exhaustive match: a rest pattern must cover the remaining elements", file, start, end);
        }
    } else if kind != TYD_UNKNOWN {
        push_error(state.3, &format!("non-exhaustive match on '{}': add a binding arm", render_key(state.0, state.1, state.2, state.6, state.7, inner)), file, start, end);
    }
}

fn variant_covered(nodes: &[i64], lists: &[Vec<i64>], arms: i64, variant: i64) -> bool {
    let count = list_len(lists, arms);
    let mut idx = 0i64;
    while idx < count {
        let pat = node_a(nodes, list_get(lists, arms, idx));
        if node_tag(nodes, pat) == NODE_PAT {
            let pkind = node_a(nodes, pat);
            if pkind == PAT_PATH || pkind == PAT_VARIANT {
                let sym = pat_sym_of(nodes, pat);
                if sym != NONE && sym_decl(nodes, sym) == variant {
                    return true;
                }
            }
        }
        idx += 1;
    }
    false
}

fn array_covers_len(nodes: &[i64], lists: &[Vec<i64>], arms: i64, n: i64) -> bool {
    let count = list_len(lists, arms);
    let mut idx = 0i64;
    while idx < count {
        let pat = node_a(nodes, list_get(lists, arms, idx));
        if node_tag(nodes, pat) == NODE_PAT && node_a(nodes, pat) == PAT_ARRAY {
            let fixed = list_len(lists, node_b(nodes, pat));
            let rest = node_c(nodes, pat);
            if rest != NONE {
                if fixed <= n {
                    return true;
                }
            } else if fixed == n {
                return true;
            }
        }
        idx += 1;
    }
    false
}

fn slice_exhaustive(nodes: &[i64], lists: &[Vec<i64>], arms: i64) -> bool {
    let count = list_len(lists, arms);
    let mut min_rest: i64 = NONE;
    let mut exacts: Vec<i64> = Vec::new();
    let mut idx = 0i64;
    while idx < count {
        let pat = node_a(nodes, list_get(lists, arms, idx));
        if node_tag(nodes, pat) == NODE_PAT && node_a(nodes, pat) == PAT_ARRAY {
            let fixed = list_len(lists, node_b(nodes, pat));
            let rest = node_c(nodes, pat);
            if rest != NONE {
                if min_rest == NONE || fixed < min_rest {
                    min_rest = fixed;
                }
            } else {
                exacts.push(fixed);
            }
        }
        idx += 1;
    }
    if min_rest == NONE {
        return false;
    }
    let mut len = 0i64;
    while len < min_rest {
        if !exacts.contains(&len) {
            return false;
        }
        len += 1;
    }
    true
}

fn resolve_all_vars(names: &mut [String], nodes: &mut Vec<i64>, lists: &mut Vec<Vec<i64>>, errors: &mut Vec<Diag>, vars: &[(i64, i64)], origins: &[(i64, i64, i64)]) {
    report_unbound(names, nodes, errors, vars, origins);
    let mut idx = 0i64;
    while idx < nodes.len() as i64 / NODE_STRIDE {
        let tag = node_tag(nodes, idx);
        if tag == NODE_EXPR {
            let resolved = resolve_key(nodes, lists, vars, expr_ty_of(nodes, idx));
            expr_set_ty(nodes, idx, resolved);
        } else if tag == NODE_STMT {
            let resolved = resolve_key(nodes, lists, vars, stmt_ty_of(nodes, idx));
            stmt_set_ty(nodes, idx, resolved);
        } else if tag == NODE_PAT {
            let resolved = resolve_key(nodes, lists, vars, pat_ty_of(nodes, idx));
            pat_set_ty(nodes, idx, resolved);
        } else if tag == NODE_TY {
            let resolved = resolve_key(nodes, lists, vars, ty_key_of(nodes, idx));
            ty_set_key(nodes, idx, resolved);
        } else if tag == NODE_INST {
            resolve_instance_row(nodes, lists, vars, idx);
        }
        idx += 1;
    }
}

fn resolve_key(nodes: &mut Vec<i64>, lists: &mut Vec<Vec<i64>>, vars: &[(i64, i64)], key: i64) -> i64 {
    if key == NONE {
        return NONE;
    }
    if is_var(key) {
        let r = resolve_var(vars, key);
        if is_var(r) {
            return r;
        }
        return resolve_key(nodes, lists, vars, r);
    }
    let row = find_tyinfo(nodes, key);
    if row == NONE {
        return key;
    }
    let kind = node_b(nodes, row);
    let sym = node_c(nodes, row);
    let args = node_d(nodes, row);
    let elem = node_e(nodes, row);
    let len = node_f(nodes, row);
    let new_args = resolve_list_keys(nodes, lists, vars, args);
    let new_elem = resolve_key(nodes, lists, vars, elem);
    if new_args == args && new_elem == elem {
        return key;
    }
    canon_tyinfo(nodes, lists, kind, sym, new_args, new_elem, len)
}

fn resolve_list_keys(nodes: &mut Vec<i64>, lists: &mut Vec<Vec<i64>>, vars: &[(i64, i64)], list: i64) -> i64 {
    let count = list_len(lists, list);
    if count == 0 {
        return list;
    }
    let mut changed = false;
    let fresh = alloc_list(lists);
    let mut idx = 0i64;
    while idx < count {
        let old = list_get(lists, list, idx);
        let new = resolve_key(nodes, lists, vars, old);
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

fn resolve_instance_row(nodes: &mut Vec<i64>, lists: &mut Vec<Vec<i64>>, vars: &[(i64, i64)], inst: i64) {
    let fn_node = inst_fn_of(nodes, inst);
    let args = inst_args_of(nodes, inst);
    let new_args = resolve_list_keys(nodes, lists, vars, args);
    let new_ret = resolve_key(nodes, lists, vars, inst_ret_of(nodes, inst));
    let new_params = resolve_list_keys(nodes, lists, vars, inst_params_of(nodes, inst));
    let mono = canon_tyinfo(nodes, lists, TYD_MONO, fn_node, new_args, NONE, NONE);
    inst_set_args(nodes, inst, new_args);
    inst_set_ret(nodes, inst, new_ret);
    inst_set_params(nodes, inst, new_params);
    inst_set_mono(nodes, inst, mono);
}

fn report_unbound(names: &[String], nodes: &mut [i64], errors: &mut Vec<Diag>, vars: &[(i64, i64)], origins: &[(i64, i64, i64)]) {
    let mut idx = 0usize;
    while idx < vars.len() {
        match vars.get(idx) {
            Some(pair) => {
                let r = resolve_var(vars, pair.0);
                if is_var(r) {
                    let origin = origin_of(origins, pair.0);
                    let what = if origin.2 == NONE {
                        String::from("a type parameter")
                    } else {
                        format!("type parameter '{}'", name_text(names, origin.2))
                    };
                    if origin.1 == NONE {
                        push_internal(errors, &format!("cannot infer {}", what));
                    } else {
                        push_error(errors, &format!("cannot infer {}", what), node_file(nodes, origin.1), node_start(nodes, origin.1), node_end(nodes, origin.1));
                    }
                }
            }
            None => break,
        }
        idx += 1;
    }
}

fn origin_of(origins: &[(i64, i64, i64)], var: i64) -> (i64, i64, i64) {
    let mut idx = 0usize;
    loop {
        match origins.get(idx) {
            Some(origin) => {
                if origin.0 == var {
                    return *origin;
                }
            }
            None => return (NONE, NONE, NONE),
        }
        idx += 1;
    }
}

#[cfg(test)]
mod tests {
    // Drives the real front end (module loading through borrow checking,
    // the same path `analysis::analyze` gives the LSP and the playground)
    // over an in-memory source, with no LLVM dependency — the only way to
    // pin typechecker behavior end to end on a machine without the LLVM
    // toolchain `cargo test`'s fixture-linked suites need.
    fn errors_for(source: &str) -> Vec<String> {
        let overlay = [("scratch.cnb".to_string(), source.to_string())];
        let result = crate::analysis::analyze("scratch.cnb", &overlay);
        result.errors.iter().map(|d| d.0.clone()).collect()
    }

    // An `impl` that leaves one of the trait's methods out used to be
    // accepted: only the methods it did provide were checked against the
    // trait, so the omission surfaced solely at a call site that happened
    // to dispatch the missing method. An impl nothing fully exercised
    // compiled clean.
    #[test]
    fn impl_missing_a_trait_method_is_rejected() {
        let source = r#"
pub trait Measure
  pub fun width(value: &Self) I64
  pub fun height(value: &Self) I64
end

pub type Card
  pub side: I64
end

pub impl Measure for Card
  pub fun width(value: &Card) I64
    return value.side
  end
end

fun width_of<T: Measure>(value: &T) I64
  return Measure.width(value)
end

pub fun main() I64
  val card = Card(side: 3)
  return width_of(&card)
end
"#;
        let errors = errors_for(source);
        assert!(
            errors.iter().any(|m| m.contains("impl of trait 'Measure' for 'Card' is missing method 'height'")),
            "{:?}",
            errors
        );
    }

    // Every missing method is named, not just the first: a diagnostic that
    // stopped at one would have the developer rebuild to find the next.
    #[test]
    fn every_missing_trait_method_is_named() {
        let source = r#"
pub trait Measure
  pub fun width(value: &Self) I64
  pub fun height(value: &Self) I64
  pub fun depth(value: &Self) I64
end

pub type Card
  pub side: I64
end

pub impl Measure for Card
  pub fun width(value: &Card) I64
    return value.side
  end
end

fun width_of<T: Measure>(value: &T) I64
  return Measure.width(value)
end

pub fun main() I64
  val card = Card(side: 3)
  return width_of(&card)
end
"#;
        let errors = errors_for(source);
        assert!(errors.iter().any(|m| m.contains("missing method 'height'")), "{:?}", errors);
        assert!(errors.iter().any(|m| m.contains("missing method 'depth'")), "{:?}", errors);
    }

    // Negative control, modelled on the trait/impl pair in
    // `tests/fixtures/spec.cnb`: a complete impl stays accepted.
    #[test]
    fn complete_impl_is_accepted() {
        let source = r#"
pub trait Measure
  pub fun width(value: &Self) I64
  pub fun height(value: &Self) I64
end

pub type Card
  pub side: I64
end

pub impl Measure for Card
  pub fun width(value: &Card) I64
    return value.side
  end
  pub fun height(value: &Card) I64
    return value.side
  end
end

fun width_of<T: Measure>(value: &T) I64
  return Measure.width(value)
end

fun height_of<T: Measure>(value: &T) I64
  return Measure.height(value)
end

pub fun main() I64
  val card = Card(side: 3)
  return width_of(&card) + height_of(&card)
end
"#;
        let errors = errors_for(source);
        assert!(errors.is_empty(), "{:?}", errors);
    }

    // Completeness is per impl: one type implementing the trait fully does
    // not excuse another that does not.
    #[test]
    fn a_second_incomplete_impl_is_rejected_on_its_own() {
        let source = r#"
pub trait Measure
  pub fun width(value: &Self) I64
  pub fun height(value: &Self) I64
end

pub type Card
  pub side: I64
end

pub type Tile
  pub edge: I64
end

pub impl Measure for Card
  pub fun width(value: &Card) I64
    return value.side
  end
  pub fun height(value: &Card) I64
    return value.side
  end
end

pub impl Measure for Tile
  pub fun width(value: &Tile) I64
    return value.edge
  end
end

fun width_of<T: Measure>(value: &T) I64
  return Measure.width(value)
end

pub fun main() I64
  val card = Card(side: 3)
  val tile = Tile(edge: 4)
  return width_of(&card) + width_of(&tile)
end
"#;
        let errors = errors_for(source);
        assert!(
            errors.iter().any(|m| m.contains("impl of trait 'Measure' for 'Tile' is missing method 'height'")),
            "{:?}",
            errors
        );
        assert!(!errors.iter().any(|m| m.contains("for 'Card' is missing")), "{:?}", errors);
    }
}

