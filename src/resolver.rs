//! Name resolution, scope construction, and casing enforcement.
//!
//! `resolve` builds a scope tree over two separate namespaces, `NS_TYPE`
//! and `NS_VALUE`, then rewrites every unresolved `EXPR_PATH`, `TY_PATH`,
//! and `PAT_PATH` segment into a `NODE_SYM` reference. It seeds the
//! built-in primitives and native surfaces, hoists top-level declarations
//! so declaration order does not matter, wires in each sibling module's
//! scope from the loader's `ext_mods`, and resolves `use` imports including
//! `as` aliases.
//!
//! The compiler-checked casing rules are enforced here, on the hoisted
//! declaration rather than at every use: a mis-cased identifier is one
//! resolver error and never reaches the typechecker.
//!
//! Two tags are assigned at this point precisely so that no later stage has
//! to recognize something by its name — the program's entry point
//! (`SYM_FUN_MAIN`) and each native operation's `NAT_*` opcode.
//!
//! **Invariants:**
//! - The symbol a name resolves to is decided here and nowhere else. A
//!   later stage that needs it reads the attached `NODE_SYM`; it does not
//!   re-walk the path and re-match segments with parallel logic.
//! - Downstream semantics key off `SYM_FUN_MAIN` and the `NAT_*` opcodes,
//!   never off a string comparison against `"main"` or a native function's
//!   name. Attaching the tag here is what makes that rule keepable.
//! - A name that does not resolve produces a diagnostic at the use site's
//!   real span, optionally carrying a hedged suggestion. It never quietly
//!   resolves to a plausible neighbour.

use crate::ast::*;
use crate::suggest;

pub const NS_TYPE: i64 = 0;
pub const NS_VALUE: i64 = 1;

type State<'a> = (
    &'a mut Vec<String>,
    &'a mut Vec<i64>,
    &'a mut Vec<Vec<i64>>,
    &'a mut Vec<Diag>,
    &'a mut Vec<Vec<i64>>,
    &'a mut Vec<i64>,
    &'a mut Vec<i64>,
    &'a mut Vec<i64>,
    &'a mut Vec<(i64, i64)>,
    &'a mut Vec<i64>,
    // Secondary notes tied to the errors this stage reports (definition-site
    // labels and hedged name suggestions), indexed like the borrow checker's.
    &'a mut Vec<Note>,
    // The item whose body is currently being resolved, innermost last.
    &'a mut Vec<i64>,
    // `(from, to)` edges between item symbols: every symbol resolved inside
    // an item is something that item depends on. Reachability is a graph
    // walk over these from `main`, not a "was this name mentioned anywhere"
    // flag — two dead functions that call each other are still dead.
    &'a mut Vec<(i64, i64)>,
);

/// The owner of references that belong to no nameable item.
///
/// An `impl` extends the type it is for rather than being something anyone
/// calls by name, and trait methods are reached by dispatch rather than by a
/// resolved path. Attributing their references here — and treating this as
/// permanently reached — keeps everything they mention alive.
///
/// That is deliberately conservative. Rejecting a program that is actually
/// correct is far worse than missing one dead impl, so the analysis errs
/// toward keeping things.
const ROOT_OWNER: i64 = -2;

/// Resolves names, and separately reports which items nothing reaches.
///
/// `deferred` receives the unused-item and unused-import diagnostics rather
/// than `errors`. What nothing uses is a whole-program property, not a
/// name-resolution one, and reporting it here would stop the pipeline before
/// the type checker ran — so a file with a type error would be told its
/// functions and imports are unused and never told what was actually wrong
/// with them. The caller reports these once the later stages have had their
/// say.
/// Where this stage puts what it has to say.
///
/// The three travel together because they are one decision — what the user
/// is told — split only by when it is said.
pub struct Diagnostics<'a> {
    pub errors: &'a mut Vec<Diag>,
    pub notes: &'a mut Vec<Note>,
    /// Reported by the caller once the later stages have run, not here.
    pub deferred: &'a mut Vec<Diag>,
}

pub fn resolve(
    names: &mut Vec<String>,
    nodes: &mut Vec<i64>,
    lists: &mut Vec<Vec<i64>>,
    diagnostics: Diagnostics,
    root: i64,
    ext_mods: &[(i64, i64)],
) -> bool {
    let Diagnostics { errors, notes, deferred } = diagnostics;
    let mut scopes: Vec<Vec<i64>> = Vec::new();
    let mut parents: Vec<i64> = Vec::new();
    let mut pubs: Vec<i64> = Vec::new();
    let mut prefixes: Vec<i64> = Vec::new();
    let mut item_scopes: Vec<(i64, i64)> = Vec::new();
    let mut used: Vec<i64> = Vec::new();
    let mut owners: Vec<i64> = Vec::new();
    let mut edges: Vec<(i64, i64)> = Vec::new();
    let empty_prefix = alloc_list(lists);
    let root_scope = alloc_scope(&mut scopes, &mut parents, &mut pubs, &mut prefixes, NONE, empty_prefix, 1);
    let mut state: State = (
        names,
        nodes,
        lists,
        errors,
        &mut scopes,
        &mut parents,
        &mut pubs,
        &mut prefixes,
        &mut item_scopes,
        &mut used,
        notes,
        &mut owners,
        &mut edges,
    );
    seed_builtins(&mut state, root_scope, root);

    collect_list(&mut state, root_scope, root);

    let mut ext_scopes: Vec<(i64, i64)> = Vec::new();
    let mut idx = 0usize;
    while idx < ext_mods.len() {
        match ext_mods.get(idx) {
            Some(pair) => {
                let mod_name = pair.0;
                let prefix = alloc_list(state.2);
                list_push(state.2, prefix, mod_name);
                let ext_scope = alloc_scope(state.4, state.5, state.6, state.7, root_scope, prefix, 1);
                let ext_sym = alloc_sym(state.1, SYM_MODULE, mod_name, NONE, root_scope, ext_scope);
                push_entry(state.4, root_scope, mod_name, ext_sym, NS_TYPE, NONE);
                ext_scopes.push((pair.0, ext_scope));
                collect_list(&mut state, ext_scope, pair.1);
            }
            None => break,
        }
        idx += 1;
    }

    resolve_imports(&mut state, root_scope, root);
    idx = 0;
    while idx < ext_mods.len() {
        match ext_mods.get(idx) {
            Some(pair) => {
                let ext_scope = ext_scope_of(&ext_scopes, pair.0);
                resolve_imports(&mut state, ext_scope, pair.1);
            }
            None => break,
        }
        idx += 1;
    }

    walk_item_list(&mut state, root_scope, root);
    idx = 0;
    while idx < ext_mods.len() {
        match ext_mods.get(idx) {
            Some(pair) => {
                let ext_scope = ext_scope_of(&ext_scopes, pair.0);
                walk_item_list(&mut state, ext_scope, pair.1);
            }
            None => break,
        }
        idx += 1;
    }

    classify_native_views(&mut state);
    link_extraction_surfaces(&mut state);

    // Deferred, for the same reason reachability is: "nothing names this
    // import" is a statement about the finished program, and reporting it
    // from here would return `false` and stop the pipeline — so a file with
    // a type or borrow error would be told which of its imports look idle
    // and never told what was actually wrong with it. The two diagnostics
    // are the same kind of fact and are reported at the same moment.
    check_unused_imports(state.0, state.1, state.2, deferred, state.9, root);
    idx = 0;
    while idx < ext_mods.len() {
        match ext_mods.get(idx) {
            Some(pair) => check_unused_imports(state.0, state.1, state.2, deferred, state.9, pair.1),
            None => break,
        }
        idx += 1;
    }

    materialize_scope_facts(&mut state);

    // Reachability last, and only if nothing else failed. A program whose
    // names do not resolve has no dependency graph worth walking, and
    // reporting every item as unused on top of the real error would bury it.
    if state.3.is_empty()
        && let Some(reached) = reachable_from_main(&state)
    {
        report_unreachable(&mut state, root, &reached, deferred);
        idx = 0;
        while idx < ext_mods.len() {
            match ext_mods.get(idx) {
                Some(pair) => report_unreachable(&mut state, pair.1, &reached, deferred),
                None => break,
            }
            idx += 1;
        }
    }

    state.3.is_empty()
}

fn materialize_scope_facts(state: &mut State) {
    let mut visible: Vec<(i64, i64, i64, i64)> = Vec::new();
    let mut members: Vec<(i64, i64, i64, i64, i64)> = Vec::new();
    let scope_count = state.4.len() as i64;
    let mut query = 0i64;
    while query < scope_count {
        let mut seen: Vec<(i64, i64)> = Vec::new();
        let mut current = query;
        while current != NONE {
            let entries = match state.4.get(current as usize) {
                Some(value) => value,
                None => break,
            };
            let count = entries.len() as i64 / 4;
            let mut idx = 0i64;
            while idx < count {
                let name = entry_get(entries, idx, 0);
                let sym = entry_get(entries, idx, 1);
                let namespace = entry_get(entries, idx, 2);
                if sym != NONE
                    && !seen.contains(&(name, namespace))
                    && is_visible(state.5, state.6, state.1, query, sym)
                {
                    visible.push((query, name, sym, namespace));
                    seen.push((name, namespace));
                }
                idx += 1;
            }
            current = parent_of(state.5, current);
        }
        let mut member_scope = 0i64;
        while member_scope < scope_count {
            let entries = match state.4.get(member_scope as usize) {
                Some(value) => value,
                None => break,
            };
            let count = entries.len() as i64 / 4;
            let mut idx = 0i64;
            while idx < count {
                let name = entry_get(entries, idx, 0);
                let sym = entry_get(entries, idx, 1);
                let namespace = entry_get(entries, idx, 2);
                if sym != NONE && is_visible(state.5, state.6, state.1, query, sym) {
                    members.push((query, member_scope, name, sym, namespace));
                }
                idx += 1;
            }
            member_scope += 1;
        }
        query += 1;
    }
    let mut visible_idx = 0usize;
    while visible_idx < visible.len() {
        match visible.get(visible_idx) {
            Some(row) => {
                alloc_scope_visible(state.1, row.0, row.1, row.2, row.3);
            }
            None => break,
        }
        visible_idx += 1;
    }
    let mut member_idx = 0usize;
    while member_idx < members.len() {
        match members.get(member_idx) {
            Some(row) => {
                alloc_scope_member(state.1, row.0, row.1, row.2, row.3, row.4);
            }
            None => break,
        }
        member_idx += 1;
    }
}

fn attach_scope(state: &mut State, source: i64, scope: i64) {
    let count = state.1.len() as i64 / NODE_STRIDE;
    let mut idx = 0i64;
    while idx < count {
        if node_tag(state.1, idx) == NODE_SCOPEFACT
            && node_a(state.1, idx) == SCOPE_AT
            && node_b(state.1, idx) == source
        {
            return;
        }
        idx += 1;
    }
    alloc_scope_at(state.1, source, scope);
}

fn alloc_scope(scopes: &mut Vec<Vec<i64>>, parents: &mut Vec<i64>, pubs: &mut Vec<i64>, prefixes: &mut Vec<i64>, parent: i64, prefix: i64, is_pub: i64) -> i64 {
    scopes.push(Vec::new());
    parents.push(parent);
    pubs.push(is_pub);
    prefixes.push(prefix);
    scopes.len() as i64 - 1
}

fn scope_prefix_of(prefixes: &[i64], scope: i64) -> i64 {
    match prefixes.get(scope as usize) {
        Some(prefix) => *prefix,
        None => NONE,
    }
}

fn parent_of(parents: &[i64], scope: i64) -> i64 {
    match parents.get(scope as usize) {
        Some(parent) => *parent,
        None => NONE,
    }
}

fn is_pub_scope(pubs: &[i64], scope: i64) -> i64 {
    match pubs.get(scope as usize) {
        Some(is_pub) => *is_pub,
        None => 0,
    }
}

fn entry_get(entries: &[i64], idx: i64, slot: i64) -> i64 {
    match entries.get((idx * 4 + slot) as usize) {
        Some(value) => *value,
        None => NONE,
    }
}

fn entry_set(entries: &mut [i64], idx: i64, slot: i64, value: i64) -> bool {
    match entries.get_mut((idx * 4 + slot) as usize) {
        Some(cell) => {
            *cell = value;
            true
        }
        None => false,
    }
}

fn push_entry(scopes: &mut [Vec<i64>], scope: i64, name: i64, sym: i64, ns: i64, src: i64) {
    if let Some(entries) = scopes.get_mut(scope as usize) {
        entries.push(name);
        entries.push(sym);
        entries.push(ns);
        entries.push(src);
    }
}

/// The symbol a name binds to in one scope, and the `use` item that bound
/// it there.
///
/// An entry still carrying `NONE` in its symbol slot binds nothing: it is
/// the placeholder `collect_item` reserves for a `use` before the path that
/// `use` names has been resolved, and the scan continues past it rather
/// than answering "this name is taken". That is what makes this lookup give
/// the same answer wherever in the file the `use` was written. A
/// placeholder sitting ahead of a real declaration of the same name used to
/// hide that declaration from `lookup_walk`, which then skipped to the
/// enclosing scope, and from `finish_import`'s conflict check, which found
/// its own placeholder and concluded the name was free — so an import
/// written above a same-name local type silently shadowed it, while the
/// same two declarations in the opposite order were correctly rejected.
fn scope_lookup(scopes: &[Vec<i64>], scope: i64, name: i64, ns: i64) -> (i64, i64) {
    let entries = match scopes.get(scope as usize) {
        Some(entries) => entries,
        None => return (NONE, NONE),
    };
    let mut idx = 0i64;
    while idx < entries.len() as i64 / 4 {
        if entry_get(entries, idx, 0) == name
            && entry_get(entries, idx, 2) == ns
            && entry_get(entries, idx, 1) != NONE
        {
            return (entry_get(entries, idx, 1), entry_get(entries, idx, 3));
        }
        idx += 1;
    }
    (NONE, NONE)
}

fn lookup_walk(scopes: &[Vec<i64>], parents: &[i64], scope: i64, name: i64, ns: i64) -> (i64, i64) {
    let mut current = scope;
    loop {
        let found = scope_lookup(scopes, current, name, ns);
        if found.0 != NONE {
            return found;
        }
        let parent = parent_of(parents, current);
        if parent == NONE {
            return (NONE, NONE);
        }
        current = parent;
    }
}

fn contains_i64(list: &[i64], needle: i64) -> bool {
    let mut idx = 0usize;
    loop {
        match list.get(idx) {
            Some(value) => {
                if *value == needle {
                    return true;
                }
            }
            None => return false,
        }
        idx += 1;
    }
}

fn alloc_sym(nodes: &mut Vec<i64>, kind: i64, name: i64, decl: i64, home: i64, sub: i64) -> i64 {
    alloc_node(nodes, &[NODE_SYM, NO_FILE, NO_FILE, NO_FILE, kind, name, decl, home, sub, NONE])
}

fn sym_kind_of(nodes: &[i64], sym: i64) -> i64 {
    node_a(nodes, sym)
}

fn sym_name_of(nodes: &[i64], sym: i64) -> i64 {
    node_b(nodes, sym)
}

fn sym_decl_of(nodes: &[i64], sym: i64) -> i64 {
    node_c(nodes, sym)
}

fn sym_home_of(nodes: &[i64], sym: i64) -> i64 {
    node_d(nodes, sym)
}

fn sym_sub_of(nodes: &[i64], sym: i64) -> i64 {
    node_e(nodes, sym)
}

fn sym_is_pub(nodes: &[i64], sym: i64) -> i64 {
    let decl = sym_decl_of(nodes, sym);
    if decl == NONE {
        return 1;
    }
    if node_tag(nodes, decl) == NODE_ITEM {
        return item_is_pub(nodes, decl);
    }
    if node_tag(nodes, decl) == NODE_VARIANT {
        return node_c(nodes, decl);
    }
    1
}

fn qualified_name(names: &mut Vec<String>, lists: &[Vec<i64>], prefix: i64, name: i64) -> i64 {
    let mut text = String::new();
    let count = list_len(lists, prefix);
    let mut idx = 0i64;
    while idx < count {
        if !text.is_empty() {
            text.push('.');
        }
        text.push_str(&name_text(names, list_get(lists, prefix, idx)));
        idx += 1;
    }
    if !text.is_empty() {
        text.push('.');
    }
    text.push_str(&name_text(names, name));
    intern(names, &text)
}

fn is_visible(parents: &[i64], pubs: &[i64], nodes: &[i64], scope: i64, sym: i64) -> bool {
    let home = sym_home_of(nodes, sym);
    let mut ancestors: Vec<i64> = Vec::new();
    let mut current = scope;
    loop {
        ancestors.push(current);
        let parent = parent_of(parents, current);
        if parent == NONE {
            break;
        }
        current = parent;
    }
    if contains_i64(&ancestors, home) {
        return true;
    }
    let mut crossed: Vec<i64> = Vec::new();
    let mut up = home;
    loop {
        if contains_i64(&ancestors, up) {
            break;
        }
        crossed.push(up);
        let parent = parent_of(parents, up);
        if parent == NONE {
            break;
        }
        up = parent;
    }
    let mut idx = 0usize;
    while let Some(scope_id) = crossed.get(idx) {
        if is_pub_scope(pubs, *scope_id) != 1 {
            return false;
        }
        idx += 1;
    }
    sym_is_pub(nodes, sym) == 1
}

fn first_char_lower(text: &str) -> bool {
    match text.chars().next() {
        Some(ch) => ch.is_ascii_lowercase(),
        None => false,
    }
}

fn first_char_upper(text: &str) -> bool {
    match text.chars().next() {
        Some(ch) => ch.is_ascii_uppercase(),
        None => false,
    }
}

fn all_lower_rest(text: &str) -> bool {
    let mut first = true;
    for ch in text.chars() {
        if first {
            first = false;
            continue;
        }
        if !ch.is_ascii_lowercase() && !ch.is_ascii_digit() && ch != '_' {
            return false;
        }
    }
    true
}

fn all_pascal_rest(text: &str) -> bool {
    let mut first = true;
    for ch in text.chars() {
        if first {
            first = false;
            continue;
        }
        if !ch.is_ascii_lowercase() && !ch.is_ascii_uppercase() && !ch.is_ascii_digit() {
            return false;
        }
    }
    true
}

fn all_screaming_rest(text: &str) -> bool {
    let mut first = true;
    for ch in text.chars() {
        if first {
            first = false;
            continue;
        }
        if !ch.is_ascii_uppercase() && !ch.is_ascii_digit() && ch != '_' {
            return false;
        }
    }
    true
}

fn casing_ok(names: &[String], name: i64, casing: i64) -> i64 {
    let text = name_text(names, name);
    if casing == 1 {
        if first_char_lower(&text) && all_lower_rest(&text) {
            return 1;
        }
    } else if casing == 2 {
        if first_char_upper(&text) && all_pascal_rest(&text) {
            return 1;
        }
    } else if casing == 3
        && (first_char_upper(&text) || text.starts_with('_')) && all_screaming_rest(&text) {
            return 1;
        }
    0
}

fn report_casing(names: &[String], name: i64, casing: i64, errors: &mut Vec<Diag>, file: i64, start: i64, end: i64) {
    if casing_ok(names, name, casing) == 0 {
        let rule = if casing == 1 {
            "snake_case"
        } else if casing == 2 {
            "PascalCase"
        } else {
            "SCREAMING_SNAKE_CASE"
        };
        push_error(errors, &format!("'{}' violates casing rule: expected {}", name_text(names, name), rule), file, start, end);
    }
}

fn insert_decl(state: &mut State, scope: i64, name: i64, sym: i64, ns: i64, casing: i64, span: (i64, i64, i64)) -> i64 {
    report_casing(state.0, name, casing, state.3, span.0, span.1, span.2);
    let existing = scope_lookup(state.4, scope, name, ns);
    if existing.0 == NONE {
        push_entry(state.4, scope, name, sym, ns, NONE);
        return 1;
    }
    let existing_decl = sym_decl_of(state.1, existing.0);
    let incoming_decl = sym_decl_of(state.1, sym);
    let builtin_collision = existing_decl == NONE
        || (existing_decl != NONE && node_file(state.1, existing_decl) == NO_FILE)
        || (incoming_decl != NONE && node_file(state.1, incoming_decl) == NO_FILE);
    let message = if builtin_collision {
        format!("cannot redeclare builtin '{}'", name_text(state.0, name))
    } else {
        format!("duplicate symbol '{}'", name_text(state.0, name))
    };
    let report_span = if incoming_decl != NONE
        && node_file(state.1, incoming_decl) == NO_FILE
        && existing_decl != NONE
        && node_file(state.1, existing_decl) != NO_FILE
    {
        (
            node_file(state.1, existing_decl),
            node_start(state.1, existing_decl),
            node_end(state.1, existing_decl),
        )
    } else {
        span
    };
    push_error(state.3, &message, report_span.0, report_span.1, report_span.2);
    // A duplicate of two real declarations: point at the first one so the
    // developer sees both sites of the clash in one diagnostic.  A builtin
    // redeclaration has no source origin to point at, so it gets no note.
    if !builtin_collision && existing_decl != NONE {
        push_note_for_last(
            state.3,
            state.10,
            "first declared here",
            node_file(state.1, existing_decl),
            node_start(state.1, existing_decl),
            node_end(state.1, existing_decl),
            NOTE_CONTEXT,
        );
    }
    0
}

fn collect_list(state: &mut State, scope: i64, list: i64) {
    let count = list_len(state.2, list);
    let mut idx = 0i64;
    while idx < count {
        collect_item(state, scope, list_get(state.2, list, idx));
        idx += 1;
    }
}

fn collect_item(state: &mut State, scope: i64, item: i64) {
    if node_tag(state.1, item) != NODE_ITEM {
        return;
    }
    let kind = node_a(state.1, item);
    let is_pub = item_is_pub(state.1, item);
    let file = node_file(state.1, item);
    let start = node_start(state.1, item);
    let end = node_end(state.1, item);
    let prefix = scope_prefix_of(state.7, scope);
    if kind == ITEM_MODULE {
        let name = node_d(state.1, item);
        let full = qualified_name(state.0, state.2, prefix, name);
        let sym = alloc_sym(state.1, SYM_MODULE, full, item, scope, NONE);
        insert_decl(state, scope, name, sym, NS_TYPE, 2, (file, start, end));
        let sub_prefix = alloc_list(state.2);
        copy_list(state.2, prefix, sub_prefix);
        list_push(state.2, sub_prefix, name);
        let sub = alloc_scope(state.4, state.5, state.6, state.7, scope, sub_prefix, is_pub);
        node_set_e(state.1, sym, sub);
        state.8.push((item, sub));
        let children = node_e(state.1, item);
        collect_list(state, sub, children);
    } else if kind == ITEM_STRUCT {
        let name = node_d(state.1, item);
        let full = qualified_name(state.0, state.2, prefix, name);
        let sym = alloc_sym(state.1, SYM_STRUCT, full, item, scope, NONE);
        insert_decl(state, scope, name, sym, NS_TYPE, 2, (file, start, end));
        item_set_sym(state.1, item, sym);
        let sub = alloc_scope(state.4, state.5, state.6, state.7, scope, prefix, 1);
        node_set_e(state.1, sym, sub);
        state.8.push((item, sub));
        enter_type_params(state.1, state.2, state.4, sub, node_f(state.1, item));
        collect_fields_casing(state.0, state.1, state.2, state.3, item, scope);
    } else if kind == ITEM_ENUM {
        let name = node_d(state.1, item);
        let full = qualified_name(state.0, state.2, prefix, name);
        let sym = alloc_sym(state.1, SYM_ENUM, full, item, scope, NONE);
        sym_set_prim_kind(state.1, sym, prim_kind_of(state.0, full));
        let declared = insert_decl(state, scope, name, sym, NS_TYPE, 2, (file, start, end));
        item_set_sym(state.1, item, sym);
        let sub = alloc_scope(state.4, state.5, state.6, state.7, scope, prefix, 1);
        node_set_e(state.1, sym, sub);
        state.8.push((item, sub));
        enter_type_params(state.1, state.2, state.4, sub, node_f(state.1, item));
        if declared == 1 {
            collect_variants(state, scope, sub, full, item);
        }
    } else if kind == ITEM_TRAIT {
        let name = node_d(state.1, item);
        let full = qualified_name(state.0, state.2, prefix, name);
        let sym = alloc_sym(state.1, SYM_TRAIT, full, item, scope, NONE);
        insert_decl(state, scope, name, sym, NS_TYPE, 2, (file, start, end));
        item_set_sym(state.1, item, sym);
        let sub = alloc_scope(state.4, state.5, state.6, state.7, scope, prefix, is_pub);
        node_set_e(state.1, sym, sub);
        state.8.push((item, sub));
        collect_trait_methods(state, sub, full, item);
    } else if kind == ITEM_IMPL {
        item_set_sym(state.1, item, NONE);
    } else if kind == ITEM_FUN || kind == ITEM_NATIVE_FUN {
        let fn_node = node_d(state.1, item);
        let name = node_a(state.1, fn_node);
        let full = qualified_name(state.0, state.2, prefix, name);
        let sym_kind = if kind == ITEM_FUN { SYM_FUN } else { SYM_NATIVE_FUN };
        let sym = alloc_sym(state.1, sym_kind, full, item, scope, NONE);
        insert_decl(state, scope, name, sym, NS_VALUE, 1, (file, start, end));
        item_set_sym(state.1, item, sym);
        if kind == ITEM_NATIVE_FUN {
            sym_set_native_op(state.1, sym, native_opcode_of(state.0, full));
        } else if full == intern(state.0, "main") {
            node_set_f(state.1, sym, SYM_FUN_MAIN);
        }
    } else if kind == ITEM_CONST {
        let name = node_d(state.1, item);
        let full = qualified_name(state.0, state.2, prefix, name);
        let sym = alloc_sym(state.1, SYM_CONST, full, item, scope, NONE);
        insert_decl(state, scope, name, sym, NS_VALUE, 3, (file, start, end));
        item_set_sym(state.1, item, sym);
    } else if kind == ITEM_NATIVE_TYPE {
        let name = node_d(state.1, item);
        let full = qualified_name(state.0, state.2, prefix, name);
        let sym = alloc_sym(state.1, SYM_TYPE, full, item, scope, NONE);
        insert_decl(state, scope, name, sym, NS_TYPE, 2, (file, start, end));
        item_set_sym(state.1, item, sym);
        let sub = alloc_scope(state.4, state.5, state.6, state.7, scope, prefix, 1);
        node_set_e(state.1, sym, sub);
        state.8.push((item, sub));
        enter_type_params(state.1, state.2, state.4, sub, node_e(state.1, item));
    } else if kind == ITEM_USE {
        let segs = node_d(state.1, item);
        let last = list_last(state.2, segs);
        let alias = node_e(state.1, item);
        let entry_name = if alias != NONE { alias } else { last };
        push_entry(state.4, scope, entry_name, NONE, 0, item);
    }
}

fn collect_fields_casing(names: &[String], nodes: &mut [i64], lists: &[Vec<i64>], errors: &mut Vec<Diag>, item: i64, scope: i64) {
    let fields = node_e(nodes, item);
    let count = list_len(lists, fields);
    let mut idx = 0i64;
    while idx < count {
        let field = list_get(lists, fields, idx);
        report_casing(names, node_a(nodes, field), 1, errors, node_file(nodes, field), node_start(nodes, field), node_end(nodes, field));
        // Slot d records the module scope the struct is declared in; the
        // typechecker compares it against the accessing scope to enforce
        // field visibility.  The scope id is a resolver fact, never
        // re-derived downstream.
        node_set_d(nodes, field, scope);
        idx += 1;
    }
}

fn enter_type_params(nodes: &mut Vec<i64>, lists: &mut [Vec<i64>], scopes: &mut [Vec<i64>], scope: i64, params: i64) {
    let count = list_len(lists, params);
    let mut idx = 0i64;
    while idx < count {
        let param = list_get(lists, params, idx);
        if node_tag(nodes, param) == NODE_TY && node_a(nodes, param) == TY_PARAM {
            let name = node_b(nodes, param);
            let sym = alloc_sym(nodes, SYM_TYPE, name, NONE, scope, NONE);
            push_entry(scopes, scope, name, sym, NS_TYPE, NONE);
        }
        idx += 1;
    }
}

fn collect_variants(state: &mut State, hoist_scope: i64, sub: i64, enum_full: i64, item: i64) {
    let variants = node_e(state.1, item);
    let count = list_len(state.2, variants);
    let mut idx = 0i64;
    while idx < count {
        let variant = list_get(state.2, variants, idx);
        let var_name = node_a(state.1, variant);
        report_casing(state.0, var_name, 2, state.3, node_file(state.1, variant), node_start(state.1, variant), node_end(state.1, variant));
        let single = single_name_list(state.2, enum_full);
        let full = qualified_name(state.0, state.2, single, var_name);
        let sym = alloc_sym(state.1, SYM_VARIANT, full, variant, sub, NONE);
        variant_set_sym(state.1, variant, sym);
        push_entry(state.4, sub, var_name, sym, NS_VALUE, NONE);
        insert_hoisted(state, hoist_scope, var_name, sym, variant);
        idx += 1;
    }
}

fn insert_hoisted(state: &mut State, scope: i64, name: i64, sym: i64, decl: i64) {
    let existing = scope_lookup(state.4, scope, name, NS_VALUE);
    if existing.0 == NONE {
        push_entry(state.4, scope, name, sym, NS_VALUE, NONE);
        return;
    }
    let existing_decl = sym_decl_of(state.1, existing.0);
    let incoming_decl = sym_decl_of(state.1, sym);
    let existing_builtin = existing_decl == NONE || node_file(state.1, existing_decl) == NO_FILE;
    let incoming_builtin = incoming_decl == NONE || node_file(state.1, incoming_decl) == NO_FILE;
    if existing.1 != NONE {
        push_error(state.3, &format!("duplicate symbol '{}'", name_text(state.0, name)), node_file(state.1, decl), node_start(state.1, decl), node_end(state.1, decl));
        return;
    }
    if existing_builtin && incoming_builtin {
        return;
    }
    if existing_builtin || incoming_builtin {
        let user_decl = if !existing_builtin { existing_decl } else { incoming_decl };
        push_error(state.3, &format!("cannot redeclare builtin '{}'", name_text(state.0, name)), node_file(state.1, user_decl), node_start(state.1, user_decl), node_end(state.1, user_decl));
        return;
    }
    push_error(state.3, &format!("duplicate symbol '{}'", name_text(state.0, name)), node_file(state.1, decl), node_start(state.1, decl), node_end(state.1, decl));
    if existing_decl != NONE && node_file(state.1, existing_decl) != NO_FILE {
        push_note_for_last(
            state.3,
            state.10,
            "first declared here",
            node_file(state.1, existing_decl),
            node_start(state.1, existing_decl),
            node_end(state.1, existing_decl),
            NOTE_CONTEXT,
        );
    }
}

fn collect_trait_methods(state: &mut State, sub: i64, trait_full: i64, item: i64) {
    let methods = node_e(state.1, item);
    let count = list_len(state.2, methods);
    let mut idx = 0i64;
    while idx < count {
        let fn_node = list_get(state.2, methods, idx);
        let name = node_a(state.1, fn_node);
        report_casing(state.0, name, 1, state.3, node_file(state.1, fn_node), node_start(state.1, fn_node), node_end(state.1, fn_node));
        let single = single_name_list(state.2, trait_full);
        let full = qualified_name(state.0, state.2, single, name);
        let sym = alloc_sym(state.1, SYM_TRAIT_METHOD, full, fn_node, sub, NONE);
        push_entry(state.4, sub, name, sym, NS_VALUE, NONE);
        idx += 1;
    }
}

fn seed_builtins(state: &mut State, root_scope: i64, root: i64) {
    let ints = builtin_int_names(state.0);
    let mut idx = 0usize;
    while idx < ints.len() {
        let name_id = match ints.get(idx) {
            Some(id) => *id,
            None => break,
        };
        let scope = seed_builtin_type(state, root_scope, name_id);
        seed_int_from(state, scope, name_id);
        idx += 1;
    }
    let bool_name = intern(state.0, "Bool");
    seed_builtin_type(state, root_scope, bool_name);
    seed_primitive(state, root, "Unit", &[], &[("Unit", &[])]);
    seed_primitive(state, root, "Result", &["T", "E"], &[("Ok", &["T"]), ("Err", &["E"])]);
    seed_primitive(state, root, "Option", &["T"], &[("Some", &["T"]), ("None", &[])]);
    seed_primitive(state, root, "DivError", &[], &[("DivByZero", &[])]);
    seed_primitive(state, root, "IndexError", &[], &[("IndexOutOfBounds", &["Usize", "Usize"])]);
}

fn seed_primitive(state: &mut State, root: i64, name: &str, params: &[&str], variants: &[(&str, &[&str])]) {
    let params_list = alloc_list(state.2);
    let mut p_idx = 0usize;
    while p_idx < params.len() {
        let param_name = match params.get(p_idx) {
            Some(text) => *text,
            None => break,
        };
        let param_id = intern(state.0, param_name);
        list_push(state.2, params_list, seed_ty_node(state.1, TY_PARAM, param_id));
        p_idx += 1;
    }
    let variants_list = alloc_list(state.2);
    let mut v_idx = 0usize;
    while v_idx < variants.len() {
        let (variant_name, payloads) = match variants.get(v_idx) {
            Some(pair) => *pair,
            None => break,
        };
        let payload_list = alloc_list(state.2);
        let mut pl_idx = 0usize;
        while pl_idx < payloads.len() {
            let payload_name = match payloads.get(pl_idx) {
                Some(text) => *text,
                None => break,
            };
            let payload_id = intern(state.0, payload_name);
            list_push(state.2, payload_list, seed_ty_node(state.1, TY_NAMED, payload_id));
            pl_idx += 1;
        }
        let var_id = intern(state.0, variant_name);
        let variant = alloc_node(state.1, &[NODE_VARIANT, NO_FILE, 0, 0, var_id, payload_list, 1]);
        list_push(state.2, variants_list, variant);
        v_idx += 1;
    }
    let name_id = intern(state.0, name);
    let item = alloc_node(
        state.1,
        &[NODE_ITEM, NO_FILE, 0, 0, ITEM_ENUM, 1, NONE, name_id, variants_list, params_list],
    );
    list_push(state.2, root, item);
}

fn seed_ty_node(nodes: &mut Vec<i64>, kind: i64, name: i64) -> i64 {
    alloc_node(nodes, &[NODE_TY, NO_FILE, 0, 0, kind, name, NONE])
}

fn seed_int_from(state: &mut State, scope: i64, name: i64) {
    let prefix = alloc_list(state.2);
    list_push(state.2, prefix, name);
    let from_name = intern(state.0, "from");
    let method = qualified_name(state.0, state.2, prefix, from_name);
    let from = alloc_sym(state.1, SYM_NATIVE_FUN, method, NONE, scope, NONE);
    sym_set_native_op(state.1, from, native_opcode_of(state.0, method));
    push_entry(state.4, scope, from_name, from, NS_VALUE, NONE);
}

fn native_opcode_of(names: &[String], full: i64) -> i64 {
    if name_is(names, full, "I8.from")
        || name_is(names, full, "I16.from")
        || name_is(names, full, "I32.from")
        || name_is(names, full, "I64.from")
        || name_is(names, full, "Isize.from")
        || name_is(names, full, "U8.from")
        || name_is(names, full, "U16.from")
        || name_is(names, full, "U32.from")
        || name_is(names, full, "U64.from")
        || name_is(names, full, "Usize.from")
    {
        return NAT_INT_FROM;
    }
    if name_is(names, full, "Slice.len") {
        return NAT_SLICE_LEN;
    }
    if name_is(names, full, "Memory.allocate") {
        return NAT_MEM_ALLOCATE;
    }
    if name_is(names, full, "Memory.deallocate") {
        return NAT_MEM_DEALLOCATE;
    }
    if name_is(names, full, "Memory.write_u8") {
        return NAT_MEM_WRITE_U8;
    }
    if name_is(names, full, "Memory.read_u8") {
        return NAT_MEM_READ_U8;
    }
    if name_is(names, full, "Collections.vec_new") {
        return NAT_VEC_NEW;
    }
    if name_is(names, full, "Collections.vec_push") {
        return NAT_VEC_PUSH;
    }
    if name_is(names, full, "Collections.vec_free") {
        return NAT_VEC_FREE;
    }
    if name_is(names, full, "Collections.vec_pop") {
        return NAT_VEC_POP;
    }
    if name_is(names, full, "Collections.string_from_slice") {
        return NAT_STRING_FROM_SLICE;
    }
    if name_is(names, full, "Collections.string_len") {
        return NAT_STRING_LEN;
    }
    if name_is(names, full, "Collections.string_free") {
        return NAT_STRING_FREE;
    }
    if name_is(names, full, "Collections.hash_map_new") {
        return NAT_HASH_MAP_NEW;
    }
    if name_is(names, full, "Collections.hash_map_insert") {
        return NAT_HASH_MAP_INSERT;
    }
    if name_is(names, full, "Collections.hash_map_get") {
        return NAT_HASH_MAP_GET;
    }
    if name_is(names, full, "Collections.hash_map_free") {
        return NAT_HASH_MAP_FREE;
    }
    if name_is(names, full, "Collections.hash_map_remove") {
        return NAT_HASH_MAP_REMOVE;
    }
    if name_is(names, full, "Runtime.self_check") {
        return NAT_SELF_CHECK;
    }
    if name_is(names, full, "Terminal.print") {
        return NAT_TERM_PRINT;
    }
    if name_is(names, full, "Terminal.print_line") {
        return NAT_TERM_PRINT_LINE;
    }
    if name_is(names, full, "Terminal.eprint") {
        return NAT_TERM_EPRINT;
    }
    if name_is(names, full, "Terminal.read_line") {
        return NAT_TERM_READ_LINE;
    }
    if name_is(names, full, "File.open") {
        return NAT_FILE_OPEN;
    }
    if name_is(names, full, "File.read") {
        return NAT_FILE_READ;
    }
    if name_is(names, full, "File.write") {
        return NAT_FILE_WRITE;
    }
    if name_is(names, full, "File.close") {
        return NAT_FILE_CLOSE;
    }
    if name_is(names, full, "Runtime.args") {
        return NAT_RUNTIME_ARGS;
    }
    if name_is(names, full, "Net.socket") {
        return NAT_NET_SOCKET;
    }
    if name_is(names, full, "Net.bind") {
        return NAT_NET_BIND;
    }
    if name_is(names, full, "Net.listen") {
        return NAT_NET_LISTEN;
    }
    if name_is(names, full, "Net.accept") {
        return NAT_NET_ACCEPT;
    }
    if name_is(names, full, "Net.send") {
        return NAT_NET_SEND;
    }
    if name_is(names, full, "Net.close") {
        return NAT_NET_CLOSE;
    }
    if name_is(names, full, "Process.spawn") {
        return NAT_PROCESS_SPAWN;
    }
    if name_is(names, full, "Process.wait") {
        return NAT_PROCESS_WAIT;
    }
    NAT_NONE
}

// Classifies native view functions from their resolved signature rather than
// their spelling.  A view is any native function whose first parameter is a
// reference to a native handle and whose return type is a slice (written as
// either `[T]` internally or `&[T]` in source).  The opcode is the only fact
// later stages need to select the uniform handle-to-slice lowering.
fn classify_native_views(state: &mut State) {
    let count = state.1.len() as i64 / NODE_STRIDE;
    let mut idx = 0i64;
    while idx < count {
        if node_tag(state.1, idx) == NODE_SYM
            && sym_kind_of(state.1, idx) == SYM_NATIVE_FUN
            && native_view_signature(state.1, state.2, idx)
        {
            sym_set_native_op(state.1, idx, NAT_SLICE_VIEW);
        }
        idx += 1;
    }
}

fn native_view_signature(nodes: &[i64], lists: &[Vec<i64>], sym: i64) -> bool {
    let decl = sym_decl_of(nodes, sym);
    if decl == NONE || node_tag(nodes, decl) != NODE_ITEM || node_a(nodes, decl) != ITEM_NATIVE_FUN {
        return false;
    }
    let fn_node = node_d(nodes, decl);
    let params = node_c(nodes, fn_node);
    if list_len(lists, params) == 0 {
        return false;
    }
    let first = list_first(lists, params);
    if first == NONE {
        return false;
    }
    let param_ty = node_b(nodes, first);
    let param_kind = node_a(nodes, param_ty);
    if param_kind != TY_REF && param_kind != TY_REF_MUT {
        return false;
    }
    let handle_ty = node_b(nodes, param_ty);
    let handle_sym = ty_sym_of(nodes, handle_ty);
    if handle_sym == NONE || node_tag(nodes, handle_sym) != NODE_SYM || sym_kind_of(nodes, handle_sym) != SYM_TYPE {
        return false;
    }
    let handle_decl = sym_decl_of(nodes, handle_sym);
    if handle_decl == NONE || node_tag(nodes, handle_decl) != NODE_ITEM || node_a(nodes, handle_decl) != ITEM_NATIVE_TYPE {
        return false;
    }
    let mut return_ty = node_d(nodes, fn_node);
    if node_a(nodes, return_ty) == TY_REF || node_a(nodes, return_ty) == TY_REF_MUT {
        return_ty = node_b(nodes, return_ty);
    }
    node_a(nodes, return_ty) == TY_SLICE
}

// Every native function with an extraction opcode (vec_pop, hash_map_remove)
// marks the container type its first parameter names as having an extraction
// surface: the typechecker's Resolvability Rule reads this flag at insertion
// sites, so the fact is computed here once, from the declared signature.
fn link_extraction_surfaces(state: &mut State) {
    let count = state.1.len() as i64 / NODE_STRIDE;
    let mut idx = 0i64;
    while idx < count {
        if node_tag(state.1, idx) == NODE_SYM && node_a(state.1, idx) == SYM_NATIVE_FUN {
            let op = sym_native_op(state.1, idx);
            if op == NAT_VEC_POP || op == NAT_HASH_MAP_REMOVE {
                let decl = sym_decl_of(state.1, idx);
                if decl != NONE && node_tag(state.1, decl) == NODE_ITEM {
                    let fn_node = node_d(state.1, decl);
                    let first = list_first(state.2, node_c(state.1, fn_node));
                    if first != NONE {
                        let cty_sym = container_type_sym(state.1, node_b(state.1, first));
                        if cty_sym != NONE {
                            node_set_f(state.1, cty_sym, idx);
                        }
                    }
                }
            }
        }
        idx += 1;
    }
}

// The resolved type symbol of a parameter type node, dereferencing any
// reference layers so `&mut Vec(T)` resolves to the Vec type symbol.
fn container_type_sym(nodes: &[i64], ty_node: i64) -> i64 {
    let mut node = ty_node;
    let mut guard = 0i64;
    loop {
        let kind = node_a(nodes, node);
        if kind == TY_REF || kind == TY_REF_MUT {
            node = node_b(nodes, node);
            guard += 1;
            if guard > 4 {
                return NONE;
            }
            continue;
        }
        break;
    }
    node_e(nodes, node)
}

fn prim_kind_of(names: &mut Vec<String>, full: i64) -> i64 {
    if full == intern(names, "Unit") {
        PRIM_UNIT
    } else if full == intern(names, "Result") {
        PRIM_RESULT
    } else if full == intern(names, "Option") {
        PRIM_OPTION
    } else if full == intern(names, "DivError") {
        PRIM_DIV_ERROR
    } else if full == intern(names, "IndexError") {
        PRIM_INDEX_ERROR
    } else {
        PRIM_NONE
    }
}

fn builtin_int_names(names: &mut Vec<String>) -> Vec<i64> {
    vec![
        intern(names, "I8"),
        intern(names, "I16"),
        intern(names, "I32"),
        intern(names, "I64"),
        intern(names, "Isize"),
        intern(names, "U8"),
        intern(names, "U16"),
        intern(names, "U32"),
        intern(names, "U64"),
        intern(names, "Usize"),
    ]
}

fn seed_builtin_type(state: &mut State, root_scope: i64, name: i64) -> i64 {
    let prefix = alloc_list(state.2);
    list_push(state.2, prefix, name);
    let sub = alloc_scope(state.4, state.5, state.6, state.7, root_scope, prefix, 1);
    let sym = alloc_sym(state.1, SYM_TYPE, name, NONE, sub, sub);
    push_entry(state.4, root_scope, name, sym, NS_TYPE, NONE);
    sub
}

fn resolve_imports(state: &mut State, scope: i64, list: i64) {
    let count = list_len(state.2, list);
    let mut idx = 0i64;
    while idx < count {
        let item = list_get(state.2, list, idx);
        resolve_import(state, scope, item);
        // A `use` inside `mod ... end` never reached here: this walk only
        // ever looked at the list it started with, never a module's own
        // child item list, even though `collect_item` already hoisted the
        // module's placeholder into its own scope (`item_scope_of`, the
        // same lookup `walk_item` uses for the identical shape). A
        // module-local import resolves against that module's own scope,
        // not the scope its `mod` block sits in — the same reasoning
        // `walk_item`'s `ITEM_MODULE` arm already applies to everything
        // else inside it.
        if node_tag(state.1, item) == NODE_ITEM && node_a(state.1, item) == ITEM_MODULE {
            let children = node_e(state.1, item);
            resolve_imports(state, item_scope_of(state.8, item), children);
        }
        idx += 1;
    }
}

fn resolve_import(state: &mut State, scope: i64, item: i64) {
    if node_tag(state.1, item) != NODE_ITEM || node_a(state.1, item) != ITEM_USE {
        return;
    }
    let segs = node_d(state.1, item);
    let file = node_file(state.1, item);
    let start = node_start(state.1, item);
    let end = node_end(state.1, item);
    let sym = resolve_path(state, scope, segs, NS_VALUE);
    if sym != NONE {
        let target_ns = sym_ns(state.1, sym);
        finish_import(state, scope, item, sym, target_ns, (file, start, end));
        return;
    }
    let type_sym = resolve_path(state, scope, segs, NS_TYPE);
    if type_sym == NONE {
        let path = join_segs(state.0, state.2, segs);
        push_error(state.3, &format!("cannot resolve import '{}'", path), file, start, end);
        return;
    }
    finish_import(state, scope, item, type_sym, NS_TYPE, (file, start, end));
}

fn finish_import(state: &mut State, scope: i64, item: i64, sym: i64, target_ns: i64, span: (i64, i64, i64)) {
    if !is_visible(state.5, state.6, state.1, scope, sym) {
        push_error(state.3, &format!("cannot import private item '{}'", name_text(state.0, sym_name_of(state.1, sym))), span.0, span.1, span.2);
        return;
    }
    let segs = node_d(state.1, item);
    let last = list_last(state.2, segs);
    let alias = node_e(state.1, item);
    let entry_name = if alias != NONE { alias } else { last };
    let casing = import_casing_of(state.1, sym);
    report_casing(state.0, entry_name, casing, state.3, span.0, span.1, span.2);
    let conflict = scope_lookup(state.4, scope, entry_name, target_ns);
    if conflict.0 != NONE && conflict.1 != item && conflict.0 != sym {
        push_error(state.3, &format!("import '{}' conflicts with another symbol", name_text(state.0, entry_name)), span.0, span.1, span.2);
        return;
    }
    // The `use` item's own symbol slot records what it resolved to, exactly
    // as every other item kind's does. Only the scope *entry* used to be
    // updated, so a `use` item's slot stayed at the parser's `NONE` forever
    // — and `check_unused`, which reads the slot to tell an import that
    // resolved from one that never did, returned on every single import
    // before it could report anything. An import that failed to resolve, or
    // that lost a conflict, still has no symbol and is still skipped there:
    // it has already been told what is wrong with it.
    item_set_sym(state.1, item, sym);
    rewrite_import(state.4, scope, item, sym, target_ns);
}

// The casing an imported name must satisfy is a property of the symbol's own
// *kind* (function, constant, variant, type, ...), not of which namespace it
// happens to resolve in: NS_VALUE holds snake_case functions but also
// SCREAMING_SNAKE_CASE constants and PascalCase enum variants, so a blanket
// per-namespace rule falsely rejects `use Config.MAX_LEN`/`use Colors.Red`.
fn import_casing_of(nodes: &[i64], sym: i64) -> i64 {
    let kind = sym_kind_of(nodes, sym);
    if kind == SYM_CONST {
        3
    } else if kind == SYM_FUN || kind == SYM_NATIVE_FUN || kind == SYM_TRAIT_METHOD || kind == SYM_IMPL_METHOD {
        1
    } else {
        2
    }
}

fn sym_ns(nodes: &[i64], sym: i64) -> i64 {
    let kind = sym_kind_of(nodes, sym);
    if kind == SYM_FUN || kind == SYM_NATIVE_FUN || kind == SYM_CONST || kind == SYM_VARIANT || kind == SYM_TRAIT_METHOD || kind == SYM_IMPL_METHOD {
        NS_VALUE
    } else {
        NS_TYPE
    }
}

fn rewrite_import(scopes: &mut [Vec<i64>], scope: i64, use_item: i64, sym: i64, ns: i64) {
    let entries = match scopes.get_mut(scope as usize) {
        Some(entries) => entries,
        None => return,
    };
    let mut idx = 0i64;
    while idx < entries.len() as i64 / 4 {
        if entry_get(entries, idx, 3) == use_item {
            entry_set(entries, idx, 1, sym);
            entry_set(entries, idx, 2, ns);
            return;
        }
        idx += 1;
    }
}

fn resolve_path(state: &mut State, scope: i64, segs: i64, final_ns: i64) -> i64 {
    let count = list_len(state.2, segs);
    if count == 0 {
        return NONE;
    }
    let mut current = scope;
    let mut idx = 0i64;
    while idx < count - 1 {
        let (sym, src) = lookup_walk(state.4, state.5, current, list_get(state.2, segs, idx), NS_TYPE);
        if sym == NONE {
            return NONE;
        }
        if src != NONE {
            mark_used(state.9, src);
        }
        let sub = sym_sub_of(state.1, sym);
        if sub == NONE {
            return NONE;
        }
        current = sub;
        idx += 1;
    }
    let (sym, src) = lookup_walk(state.4, state.5, current, list_get(state.2, segs, count - 1), final_ns);
    if sym != NONE && src != NONE {
        mark_used(state.9, src);
    }
    record_dependency(state, sym);
    sym
}

// Records that the item currently being resolved depends on `sym`.
//
// A reference outside any item — there are none today, but the stack is
// empty before the first item and after the last — is attributed to the
// permanent root rather than dropped, so it can only ever keep something
// alive, never kill it.
fn record_dependency(state: &mut State, sym: i64) {
    if sym == NONE {
        return;
    }
    let owner = match state.11.last() {
        Some(value) => *value,
        None => ROOT_OWNER,
    };
    if owner == sym {
        return;
    }
    if !state.12.iter().any(|edge| edge.0 == owner && edge.1 == sym) {
        state.12.push((owner, sym));
    }
}

/// Every item symbol reachable from `main`, or `None` when there is no
/// `main` to reach from.
///
/// A compilation unit without an entry point is not a whole program, and
/// reachability is a whole-program property: `build.cnb` is three `pub const`
/// declarations, and a module compiled on its own is a module. Answering
/// "everything is unreachable" for either would be answering a question
/// nobody asked.
///
/// This is not an escape hatch. A program with no `main` cannot be built
/// into a binary at all, so nothing that ships can take this path.
fn reachable_from_main(state: &State) -> Option<Vec<i64>> {
    let mut reached: Vec<i64> = vec![ROOT_OWNER];
    let mut found_main = false;
    let mut idx = 0i64;
    while idx < state.1.len() as i64 / NODE_STRIDE {
        // The kind matters as well as the flag: `SYM_FUN_MAIN` is 1, and the
        // `f` slot means something else for other symbol kinds, so without
        // the kind check any symbol whose `f` happened to hold 1 counted as
        // an entry point.
        if node_tag(state.1, idx) == NODE_SYM
            && node_a(state.1, idx) == SYM_FUN
            && node_f(state.1, idx) == SYM_FUN_MAIN
        {
            reached.push(idx);
            found_main = true;
        }
        idx += 1;
    }
    if !found_main {
        return None;
    }
    // Fixpoint rather than a single pass: an item pulled in by a later edge
    // brings its own dependencies with it.
    let mut grew = true;
    while grew {
        grew = false;
        let mut edge_idx = 0usize;
        while edge_idx < state.12.len() {
            match state.12.get(edge_idx) {
                Some(edge) => {
                    if contains_i64(&reached, edge.0) && !contains_i64(&reached, edge.1) {
                        reached.push(edge.1);
                        grew = true;
                    }
                }
                None => break,
            }
            edge_idx += 1;
        }
    }
    Some(reached)
}

/// The word for an item kind in an "unused ..." diagnostic, and whether the
/// kind is one reachability applies to at all.
fn unreachable_label(kind: i64) -> Option<&'static str> {
    if kind == ITEM_FUN {
        Some("function")
    } else if kind == ITEM_NATIVE_FUN {
        Some("native function")
    } else if kind == ITEM_CONST {
        Some("constant")
    } else if kind == ITEM_STRUCT {
        Some("struct")
    } else if kind == ITEM_ENUM {
        Some("enum")
    } else if kind == ITEM_TRAIT {
        Some("trait")
    } else if kind == ITEM_NATIVE_TYPE {
        Some("native type")
    } else {
        // Modules are namespaces, `use` items have their own unused check,
        // and impls extend the type they are for.
        None
    }
}

/// Whether any variant of the enum declared by `item` is reached.
fn enum_variant_reached(state: &State, item: i64, reached: &[i64]) -> bool {
    let variants = node_e(state.1, item);
    let count = list_len(state.2, variants);
    let mut idx = 0i64;
    while idx < count {
        let variant = list_get(state.2, variants, idx);
        if contains_i64(reached, variant_sym_of(state.1, variant)) {
            return true;
        }
        idx += 1;
    }
    false
}

/// Reports every declared item that nothing reachable from `main` needs.
///
/// Public and private alike: `pub` describes who may name a thing, not
/// whether anything does. Exempting it would make `pub` the one-word way to
/// silence this diagnostic, which is the suppression mechanism the language
/// does not have.
fn report_unreachable(state: &mut State, list: i64, reached: &[i64], deferred: &mut Vec<Diag>) {
    let count = list_len(state.2, list);
    let mut idx = 0i64;
    while idx < count {
        let item = list_get(state.2, list, idx);
        idx += 1;
        if node_tag(state.1, item) != NODE_ITEM {
            continue;
        }
        let kind = node_a(state.1, item);
        if kind == ITEM_MODULE {
            report_unreachable(state, node_e(state.1, item), reached, deferred);
            continue;
        }
        // A seeded builtin has no Cinnabar source behind it — `Result`,
        // `Option`, `DivError` and `IndexError` are injected by the resolver,
        // carry `NO_FILE`, and cannot be deleted by anyone. Telling a
        // three-line program that `Result` is unused would be reporting the
        // compiler's own declarations back at its user.
        if node_file(state.1, item) == NO_FILE {
            continue;
        }
        let label = match unreachable_label(kind) {
            Some(text) => text,
            None => continue,
        };
        let sym = item_sym_of(state.1, item);
        if sym == NONE || contains_i64(reached, sym) {
            continue;
        }
        // Constructing a variant reaches the enum. `[T1(4), T2(3, 4), T0]`
        // never names `Tag`, but an enum whose variants are in use is not
        // dead — the type is exactly what those constructions produce.
        if kind == ITEM_ENUM && enum_variant_reached(state, item, reached) {
            continue;
        }
        if node_f(state.1, sym) == SYM_FUN_MAIN {
            continue;
        }
        let name = if kind == ITEM_FUN || kind == ITEM_NATIVE_FUN {
            node_a(state.1, node_d(state.1, item))
        } else {
            node_d(state.1, item)
        };
        let text = format!("unused {} '{}'", label, name_text(state.0, name));
        push_error(
            deferred,
            &text,
            node_file(state.1, item),
            node_start(state.1, item),
            node_end(state.1, item),
        );
    }
}

fn mark_used(used: &mut Vec<i64>, use_item: i64) {
    if !contains_i64(used, use_item) {
        used.push(use_item);
    }
}


fn join_segs(names: &[String], lists: &[Vec<i64>], segs: i64) -> String {
    let mut text = String::new();
    let count = list_len(lists, segs);
    let mut idx = 0i64;
    while idx < count {
        if !text.is_empty() {
            text.push('.');
        }
        text.push_str(&name_text(names, list_get(lists, segs, idx)));
        idx += 1;
    }
    text
}

fn single_name_list(lists: &mut Vec<Vec<i64>>, name: i64) -> i64 {
    let list = alloc_list(lists);
    list_push(lists, list, name);
    list
}

fn copy_list(lists: &mut [Vec<i64>], from: i64, to: i64) {
    let count = list_len(lists, from);
    let mut idx = 0i64;
    while idx < count {
        let item = list_get(lists, from, idx);
        list_push(lists, to, item);
        idx += 1;
    }
}

fn ext_scope_of(ext_scopes: &[(i64, i64)], name: i64) -> i64 {
    let mut idx = 0usize;
    loop {
        match ext_scopes.get(idx) {
            Some(pair) => {
                if pair.0 == name {
                    return pair.1;
                }
            }
            None => return 0,
        }
        idx += 1;
    }
}

fn walk_item_list(state: &mut State, scope: i64, list: i64) {
    let count = list_len(state.2, list);
    let mut idx = 0i64;
    while idx < count {
        walk_item(state, scope, list_get(state.2, list, idx));
        idx += 1;
    }
}

fn walk_item(state: &mut State, scope: i64, item: i64) {
    if node_tag(state.1, item) != NODE_ITEM {
        return;
    }
    let kind = node_a(state.1, item);
    // A module is a namespace rather than a thing to keep alive: its
    // children are each checked on their own, so it owns nothing.
    let owner = if kind == ITEM_MODULE {
        NONE
    } else if kind == ITEM_IMPL {
        ROOT_OWNER
    } else {
        let sym = item_sym_of(state.1, item);
        if sym == NONE { ROOT_OWNER } else { sym }
    };
    if owner != NONE {
        state.11.push(owner);
    }
    let item_scope = if kind == ITEM_MODULE {
        item_scope_of(state.8, item)
    } else {
        scope
    };
    attach_scope(state, item, item_scope);
    if kind == ITEM_MODULE {
        let children = node_e(state.1, item);
        walk_item_list(state, item_scope_of(state.8, item), children);
    } else if kind == ITEM_STRUCT {
        walk_fields(state, item_scope_of(state.8, item), item);
    } else if kind == ITEM_ENUM {
        walk_variants(state, item_scope_of(state.8, item), item);
    } else if kind == ITEM_TRAIT {
        walk_fn_list(state, scope, node_e(state.1, item));
    } else if kind == ITEM_IMPL {
        resolve_impl(state, scope, item);
    } else if kind == ITEM_FUN || kind == ITEM_NATIVE_FUN {
        walk_fn(state, scope, node_d(state.1, item));
    } else if kind == ITEM_CONST {
        walk_type(state, scope, node_e(state.1, item));
        walk_expr(state, scope, node_f(state.1, item));
    }
    if owner != NONE {
        state.11.pop();
    }
}

fn item_scope_of(item_scopes: &[(i64, i64)], item: i64) -> i64 {
    let mut idx = 0usize;
    loop {
        match item_scopes.get(idx) {
            Some(pair) => {
                if pair.0 == item {
                    return pair.1;
                }
            }
            None => return 0,
        }
        idx += 1;
    }
}

fn walk_fields(state: &mut State, scope: i64, item: i64) {
    let fields = node_e(state.1, item);
    let count = list_len(state.2, fields);
    let mut idx = 0i64;
    while idx < count {
        let field = list_get(state.2, fields, idx);
        walk_type(state, scope, node_b(state.1, field));
        idx += 1;
    }
    walk_type_params(state, scope, node_f(state.1, item));
}

fn walk_variants(state: &mut State, scope: i64, item: i64) {
    let variants = node_e(state.1, item);
    let count = list_len(state.2, variants);
    let mut idx = 0i64;
    while idx < count {
        let variant = list_get(state.2, variants, idx);
        walk_type_list(state, scope, node_b(state.1, variant));
        idx += 1;
    }
    walk_type_params(state, scope, node_f(state.1, item));
}

fn walk_type_params(state: &mut State, scope: i64, params: i64) {
    let count = list_len(state.2, params);
    let mut idx = 0i64;
    while idx < count {
        let param = list_get(state.2, params, idx);
        if node_tag(state.1, param) == NODE_TY && node_a(state.1, param) == TY_PARAM {
            report_casing(state.0, node_b(state.1, param), 2, state.3, node_file(state.1, param), node_start(state.1, param), node_end(state.1, param));
            if node_c(state.1, param) != NONE {
                resolve_param_bound(state, scope, param);
            }
        }
        idx += 1;
    }
}

fn resolve_param_bound(state: &mut State, scope: i64, param: i64) {
    let segs = node_c(state.1, param);
    let sym = resolve_path(state, scope, segs, NS_TYPE);
    if sym == NONE {
        push_error(state.3, &format!("cannot resolve trait bound '{}'", join_segs(state.0, state.2, segs)), node_file(state.1, param), node_start(state.1, param), node_end(state.1, param));
        return;
    }
    if !is_visible(state.5, state.6, state.1, scope, sym) {
        push_error(state.3, &format!("cannot access trait '{}' here", name_text(state.0, sym_name_of(state.1, sym))), node_file(state.1, param), node_start(state.1, param), node_end(state.1, param));
        return;
    }
    node_set_c(state.1, param, sym);
}

fn walk_type_list(state: &mut State, scope: i64, list: i64) {
    let count = list_len(state.2, list);
    let mut idx = 0i64;
    while idx < count {
        walk_type(state, scope, list_get(state.2, list, idx));
        idx += 1;
    }
}

fn resolve_impl(state: &mut State, scope: i64, item: i64) {
    let trait_segs = node_d(state.1, item);
    let trait_sym = resolve_path(state, scope, trait_segs, NS_TYPE);
    if trait_sym == NONE {
        push_error(state.3, &format!("cannot resolve trait '{}'", join_segs(state.0, state.2, trait_segs)), node_file(state.1, item), node_start(state.1, item), node_end(state.1, item));
    } else if sym_kind_of(state.1, trait_sym) != SYM_TRAIT {
        push_error(state.3, "'impl' target is not a trait", node_file(state.1, item), node_start(state.1, item), node_end(state.1, item));
    } else {
        if !is_visible(state.5, state.6, state.1, scope, trait_sym) {
            push_error(state.3, &format!("cannot access trait '{}' here", name_text(state.0, sym_name_of(state.1, trait_sym))), node_file(state.1, item), node_start(state.1, item), node_end(state.1, item));
        }
        item_set_sym(state.1, item, trait_sym);
    }
    walk_type(state, scope, node_e(state.1, item));
    walk_fn_list(state, scope, node_f(state.1, item));
}

fn walk_fn_list(state: &mut State, scope: i64, list: i64) {
    let count = list_len(state.2, list);
    let mut idx = 0i64;
    while idx < count {
        walk_fn(state, scope, list_get(state.2, list, idx));
        idx += 1;
    }
}

fn walk_fn(state: &mut State, scope: i64, fn_node: i64) {
    if node_tag(state.1, fn_node) != NODE_FN {
        return;
    }
    let prefix = scope_prefix_of(state.7, scope);
    let param_scope = alloc_scope(state.4, state.5, state.6, state.7, scope, prefix, 1);
    attach_scope(state, fn_node, param_scope);
    enter_type_params(state.1, state.2, state.4, param_scope, node_b(state.1, fn_node));
    walk_type_params(state, scope, node_b(state.1, fn_node));
    let params = node_c(state.1, fn_node);
    let count = list_len(state.2, params);
    let mut idx = 0i64;
    while idx < count {
        let param = list_get(state.2, params, idx);
        walk_type(state, param_scope, node_b(state.1, param));
        idx += 1;
    }
    walk_type(state, param_scope, node_d(state.1, fn_node));
    walk_stmt_list(state, param_scope, node_f(state.1, fn_node));
}

fn walk_stmt_list(state: &mut State, scope: i64, list: i64) {
    let count = list_len(state.2, list);
    let mut idx = 0i64;
    while idx < count {
        walk_stmt(state, scope, list_get(state.2, list, idx));
        idx += 1;
    }
}

fn walk_stmt(state: &mut State, scope: i64, stmt: i64) {
    if node_tag(state.1, stmt) != NODE_STMT {
        return;
    }
    attach_scope(state, stmt, scope);
    let kind = node_a(state.1, stmt);
    if kind == STMT_LET {
        if node_d(state.1, stmt) != NONE {
            walk_type(state, scope, node_d(state.1, stmt));
        }
        walk_expr(state, scope, node_e(state.1, stmt));
    } else if kind == STMT_ASSIGN {
        walk_expr(state, scope, node_b(state.1, stmt));
        walk_expr(state, scope, node_c(state.1, stmt));
    } else if kind == STMT_WHILE {
        walk_expr(state, scope, node_b(state.1, stmt));
        walk_stmt_list(state, scope, node_c(state.1, stmt));
    } else if kind == STMT_IF {
        walk_expr(state, scope, node_b(state.1, stmt));
        walk_stmt_list(state, scope, node_c(state.1, stmt));
        if node_d(state.1, stmt) != NONE {
            walk_stmt_list(state, scope, node_d(state.1, stmt));
        }
    } else if kind == STMT_RETURN {
        if node_b(state.1, stmt) != NONE {
            walk_expr(state, scope, node_b(state.1, stmt));
        }
    } else if kind == STMT_EXPR {
        walk_expr(state, scope, node_b(state.1, stmt));
    }
}

fn walk_expr(state: &mut State, scope: i64, expr: i64) {
    if node_tag(state.1, expr) != NODE_EXPR {
        return;
    }
    attach_scope(state, expr, scope);
    let kind = node_a(state.1, expr);
    if kind == EXPR_PATH {
        resolve_expr_path(state, scope, expr);
    } else if kind == EXPR_UNARY {
        walk_expr(state, scope, node_c(state.1, expr));
    } else if kind == EXPR_BINARY {
        walk_expr(state, scope, node_c(state.1, expr));
        walk_expr(state, scope, node_d(state.1, expr));
    } else if kind == EXPR_CALL {
        walk_call(state, scope, expr);
    } else if kind == EXPR_STRUCT_LIT {
        walk_struct_lit(state, scope, expr);
    } else if kind == EXPR_ARRAY {
        walk_expr_list(state, scope, node_b(state.1, expr));
    } else if kind == EXPR_MATCH {
        walk_expr(state, scope, node_b(state.1, expr));
        walk_arms(state, scope, node_c(state.1, expr));
    } else if kind == EXPR_TRY {
        walk_expr(state, scope, node_b(state.1, expr));
    } else if kind == EXPR_INDEX {
        walk_expr(state, scope, node_b(state.1, expr));
        walk_expr(state, scope, node_c(state.1, expr));
    } else if kind == EXPR_FIELD_ACCESS {
        walk_expr(state, scope, node_b(state.1, expr));
    }
}

fn walk_expr_list(state: &mut State, scope: i64, list: i64) {
    let count = list_len(state.2, list);
    let mut idx = 0i64;
    while idx < count {
        walk_expr(state, scope, list_get(state.2, list, idx));
        idx += 1;
    }
}

fn walk_arms(state: &mut State, scope: i64, list: i64) {
    let count = list_len(state.2, list);
    let mut idx = 0i64;
    while idx < count {
        let arm = list_get(state.2, list, idx);
        walk_pattern(state, scope, node_a(state.1, arm));
        walk_stmt(state, scope, node_b(state.1, arm));
        idx += 1;
    }
}

fn resolve_expr_path(state: &mut State, scope: i64, expr: i64) {
    let segs = node_b(state.1, expr);
    let sym = resolve_path(state, scope, segs, NS_VALUE);
    if sym == NONE {
        return;
    }
    if !is_visible(state.5, state.6, state.1, scope, sym) {
        push_error(state.3, &format!("cannot access '{}' here", name_text(state.0, sym_name_of(state.1, sym))), node_file(state.1, expr), node_start(state.1, expr), node_end(state.1, expr));
        return;
    }
    expr_set_sym(state.1, expr, sym);
}

fn walk_call(state: &mut State, scope: i64, expr: i64) {
    let callee = node_b(state.1, expr);
    if node_tag(state.1, callee) == NODE_EXPR && node_a(state.1, callee) == EXPR_PATH {
        let segs = node_b(state.1, callee);
        let sym = resolve_path(state, scope, segs, NS_VALUE);
        if sym != NONE {
            let kind = sym_kind_of(state.1, sym);
            if kind == SYM_VARIANT || kind == SYM_STRUCT || kind == SYM_ENUM {
                node_set_a(state.1, expr, EXPR_STRUCT_LIT);
                node_set_b(state.1, expr, segs);
                node_set_c(state.1, expr, NONE);
                expr_set_sym(state.1, expr, sym);
                walk_expr_list(state, scope, node_d(state.1, expr));
                return;
            }
            if !is_visible(state.5, state.6, state.1, scope, sym) {
                push_error(state.3, &format!("cannot call '{}' here", name_text(state.0, sym_name_of(state.1, sym))), node_file(state.1, expr), node_start(state.1, expr), node_end(state.1, expr));
            } else {
                expr_set_sym(state.1, callee, sym);
            }
        }
    }
    if node_c(state.1, expr) != NONE {
        walk_type_list(state, scope, node_c(state.1, expr));
    }
    walk_expr_list(state, scope, node_d(state.1, expr));
}

fn walk_struct_lit(state: &mut State, scope: i64, expr: i64) {
    let segs = node_b(state.1, expr);
    let file = node_file(state.1, expr);
    let start = node_start(state.1, expr);
    let end = node_end(state.1, expr);
    if list_len(state.2, segs) > 1 {
        push_error(state.3, "qualified struct initialization is not allowed", file, start, end);
        return;
    }
    let sym = resolve_path(state, scope, segs, NS_TYPE);
    if sym == NONE {
        push_error(state.3, &format!("unknown type '{}'", join_segs(state.0, state.2, segs)), file, start, end);
        let first = list_first(state.2, segs);
        if first != NONE {
            suggest_type_name(state, scope, first);
        }
        return;
    }
    if !is_visible(state.5, state.6, state.1, scope, sym) {
        push_error(state.3, &format!("cannot access type '{}' here", name_text(state.0, sym_name_of(state.1, sym))), file, start, end);
        return;
    }
    expr_set_sym(state.1, expr, sym);
    walk_expr_list(state, scope, node_d(state.1, expr));
}

fn walk_pattern(state: &mut State, scope: i64, pat: i64) {
    if node_tag(state.1, pat) != NODE_PAT {
        return;
    }
    attach_scope(state, pat, scope);
    let kind = node_a(state.1, pat);
    if kind == PAT_BIND {
        let name = node_b(state.1, pat);
        let (sym, src) = lookup_walk(state.4, state.5, scope, name, NS_VALUE);
        if sym == NONE {
            return;
        }
        if src != NONE {
            mark_used(state.9, src);
        }
        if sym_kind_of(state.1, sym) != SYM_VARIANT || !is_visible(state.5, state.6, state.1, scope, sym) {
            push_error(state.3, &format!("'{}' is not a variant pattern", name_text(state.0, name)), node_file(state.1, pat), node_start(state.1, pat), node_end(state.1, pat));
            return;
        }
        let segs = single_name_list(state.2, name);
        node_set_a(state.1, pat, PAT_PATH);
        node_set_b(state.1, pat, segs);
        pat_set_sym(state.1, pat, sym);
    } else if kind == PAT_PATH {
        resolve_pat_path(state, scope, pat);
    } else if kind == PAT_VARIANT {
        resolve_pat_path(state, scope, pat);
        walk_pattern_list(state, scope, node_c(state.1, pat));
    } else if kind == PAT_ARRAY {
        walk_pattern_list(state, scope, node_b(state.1, pat));
    }
}

fn resolve_pat_path(state: &mut State, scope: i64, pat: i64) {
    let segs = node_b(state.1, pat);
    let sym = resolve_path(state, scope, segs, NS_VALUE);
    if sym == NONE {
        push_error(state.3, &format!("cannot resolve pattern '{}'", join_segs(state.0, state.2, segs)), node_file(state.1, pat), node_start(state.1, pat), node_end(state.1, pat));
        return;
    }
    if !is_visible(state.5, state.6, state.1, scope, sym) {
        push_error(state.3, &format!("cannot access '{}' here", name_text(state.0, sym_name_of(state.1, sym))), node_file(state.1, pat), node_start(state.1, pat), node_end(state.1, pat));
        return;
    }
    pat_set_sym(state.1, pat, sym);
}

fn walk_pattern_list(state: &mut State, scope: i64, list: i64) {
    let count = list_len(state.2, list);
    let mut idx = 0i64;
    while idx < count {
        walk_pattern(state, scope, list_get(state.2, list, idx));
        idx += 1;
    }
}

fn walk_type(state: &mut State, scope: i64, ty: i64) {
    if node_tag(state.1, ty) != NODE_TY {
        return;
    }
    attach_scope(state, ty, scope);
    let kind = node_a(state.1, ty);
    if kind == TY_NAMED {
        resolve_type_name(state, scope, ty, node_b(state.1, ty));
    } else if kind == TY_PATH {
        resolve_type_path(state, scope, ty);
    } else if kind == TY_GENERIC {
        resolve_type_path(state, scope, ty);
        walk_type_list(state, scope, node_c(state.1, ty));
    } else if kind == TY_REF || kind == TY_REF_MUT || kind == TY_SLICE || kind == TY_ARRAY {
        walk_type(state, scope, node_b(state.1, ty));
    }
}

fn resolve_type_name(state: &mut State, scope: i64, ty: i64, name: i64) {
    let (sym, src) = lookup_walk(state.4, state.5, scope, name, NS_TYPE);
    if sym == NONE {
        push_error(state.3, &format!("unknown type '{}'", name_text(state.0, name)), node_file(state.1, ty), node_start(state.1, ty), node_end(state.1, ty));
        suggest_type_name(state, scope, name);
        return;
    }
    if src != NONE {
        mark_used(state.9, src);
    }
    // A single-identifier type never goes through `resolve_path`, so the
    // dependency has to be recorded here too. Without it a function's own
    // return type counts for nothing, and `main() ExitCode` reports
    // `ExitCode` as unused.
    record_dependency(state, sym);
    if !is_visible(state.5, state.6, state.1, scope, sym) {
        push_error(state.3, &format!("cannot access type '{}' here", name_text(state.0, name)), node_file(state.1, ty), node_start(state.1, ty), node_end(state.1, ty));
        return;
    }
    ty_set_sym(state.1, ty, sym);
}

fn resolve_type_path(state: &mut State, scope: i64, ty: i64) {
    let segs = node_b(state.1, ty);
    let sym = resolve_path(state, scope, segs, NS_TYPE);
    if sym == NONE {
        push_error(state.3, &format!("cannot resolve type '{}'", join_segs(state.0, state.2, segs)), node_file(state.1, ty), node_start(state.1, ty), node_end(state.1, ty));
        if list_len(state.2, segs) == 1 {
            let first = list_first(state.2, segs);
            if first != NONE {
                suggest_type_name(state, scope, first);
            }
        }
        return;
    }
    if !is_visible(state.5, state.6, state.1, scope, sym) {
        push_error(state.3, &format!("cannot access type '{}' here", name_text(state.0, sym_name_of(state.1, sym))), node_file(state.1, ty), node_start(state.1, ty), node_end(state.1, ty));
        return;
    }
    ty_set_sym(state.1, ty, sym);
}

fn check_unused_imports(names: &[String], nodes: &[i64], lists: &[Vec<i64>], deferred: &mut Vec<Diag>, used: &[i64], list: i64) {
    let count = list_len(lists, list);
    let mut idx = 0i64;
    while idx < count {
        let item = list_get(lists, list, idx);
        check_unused(names, nodes, lists, deferred, used, item);
        idx += 1;
    }
}

/// Reports a `use` that resolved to something no name in the file went on
/// to reach.
///
/// The symbol slot is what separates the two failures a `use` can have: an
/// import that never resolved has none, and has already been told so — it
/// must not be told a second time that nothing uses what it does not name.
/// `mark_used` records the item every time a lookup returns through its
/// scope entry, so "used" here means a name actually resolved through this
/// import, not that its text appears somewhere.
fn check_unused(names: &[String], nodes: &[i64], lists: &[Vec<i64>], deferred: &mut Vec<Diag>, used: &[i64], item: i64) {
    if node_tag(nodes, item) != NODE_ITEM {
        return;
    }
    let kind = node_a(nodes, item);
    if kind == ITEM_MODULE {
        let children = node_e(nodes, item);
        check_unused_imports(names, nodes, lists, deferred, used, children);
        return;
    }
    if kind != ITEM_USE {
        return;
    }
    if item_is_pub(nodes, item) == 1 {
        return;
    }
    let sym = item_sym_of(nodes, item);
    if sym == NONE {
        return;
    }
    if contains_i64(used, item) {
        return;
    }
    let segs = node_d(nodes, item);
    let alias = node_e(nodes, item);
    let name = if alias != NONE { alias } else { list_last(lists, segs) };
    push_error(
        deferred,
        &format!("unused import '{}'", name_text(names, name)),
        node_file(nodes, item),
        node_start(nodes, item),
        node_end(nodes, item),
    );
}

// ---------------------------------------------------------------------------
// Dead code and unresolved-name suggestions
// ---------------------------------------------------------------------------

// The visible type-namespace names from `scope` up through its parents, as
// (name, file, start, end) for the declaration each name points at.  This
// reads the resolver's own scope table — the same entries `resolve_type_name`
// walks — so a suggestion is offered from the names actually in scope rather
// than from a second, parallel registry.
fn visible_type_names(state: &State, scope: i64) -> Vec<(String, i64, i64, i64)> {
    let mut out: Vec<(String, i64, i64, i64)> = Vec::new();
    let mut seen: Vec<i64> = Vec::new();
    let mut current = scope;
    while current != NONE {
        let entries = match state.4.get(current as usize) {
            Some(value) => value,
            None => break,
        };
        let count = entries.len() as i64 / 4;
        let mut idx = 0i64;
        while idx < count {
            let name = entry_get(entries, idx, 0);
            let sym = entry_get(entries, idx, 1);
            let ns = entry_get(entries, idx, 2);
            if ns == NS_TYPE
                && sym != NONE
                && !contains_i64(&seen, name)
                && is_visible(state.5, state.6, state.1, scope, sym)
            {
                seen.push(name);
                let decl = sym_decl_of(state.1, sym);
                if decl != NONE && node_tag(state.1, decl) == NODE_ITEM && node_file(state.1, decl) != NO_FILE {
                    out.push((
                        name_text(state.0, name),
                        node_file(state.1, decl),
                        node_start(state.1, decl),
                        node_end(state.1, decl),
                    ));
                }
            }
            idx += 1;
        }
        current = parent_of(state.5, current);
    }
    out
}

// Offer a hedged "did you mean" note for an unresolved type name, pointing
// at the candidate declaration when the match is unambiguous.  The error
// must already be pushed so the note attaches to it.
fn suggest_type_name(state: &mut State, scope: i64, misspelled: i64) {
    let text = name_text(state.0, misspelled);
    let entries = visible_type_names(state, scope);
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
        push_note_for_last(state.3, state.10, &suggestion.message, suggestion.file, suggestion.start, suggestion.end, NOTE_GUIDANCE);
    }
}

#[cfg(test)]
mod tests {
    // Drives the real front end (module loading through borrow checking,
    // the same path `analysis::analyze` gives the LSP and the playground)
    // over an in-memory source, with no LLVM dependency — the only way to
    // pin resolver behavior end to end on a machine without the LLVM
    // toolchain `cargo test`'s fixture-linked suites need.
    fn errors_for(source: &str) -> Vec<String> {
        let overlay = [("scratch.cnb".to_string(), source.to_string())];
        let result = crate::analysis::analyze("scratch.cnb", &overlay);
        result.errors.iter().map(|d| d.0.clone()).collect()
    }

    // An import nothing names is an error (Manifesto, "Compile-Time
    // Correctness": unused imports). `check_unused` reads the `use` item's
    // own symbol slot to tell a resolved import from one that never
    // resolved, and nothing ever wrote that slot — so the guard was true
    // for every import in every program and this diagnostic could not fire
    // at all. `finish_import` now records what the import resolved to.
    #[test]
    fn unused_import_is_rejected() {
        let source = r#"
pub mod Other
  pub fun helper() I64
    return 7
  end
  pub fun spare() I64
    return 9
  end
end

use Other.helper
use Other.spare

pub fun main() I64
  return helper()
end
"#;
        let errors = errors_for(source);
        assert!(errors.iter().any(|m| m.contains("unused import 'spare'")), "{:?}", errors);
    }

    // The alias is what the diagnostic must name, since the alias is the
    // name the program failed to use.
    #[test]
    fn unused_aliased_import_is_rejected_under_its_alias() {
        let source = r#"
pub mod Other
  pub fun helper() I64
    return 7
  end
  pub fun spare() I64
    return 9
  end
end

use Other.helper
use Other.spare as reserve

pub fun main() I64
  return helper()
end
"#;
        let errors = errors_for(source);
        assert!(errors.iter().any(|m| m.contains("unused import 'reserve'")), "{:?}", errors);
    }

    // Negative control: an import the program actually uses stays accepted,
    // and turning the check on must not make a clean program fail.
    #[test]
    fn used_import_is_accepted() {
        let source = r#"
pub mod Other
  pub fun helper() I64
    return 7
  end
end

use Other.helper

pub fun main() I64
  return helper()
end
"#;
        let errors = errors_for(source);
        assert!(errors.is_empty(), "{:?}", errors);
    }

    // An unused import must not answer a question nobody asked: a program
    // with a real type error is told about the type error. This is why the
    // check reports through `deferred` — reporting it from the resolver
    // would return `false` and the later stages would never run at all.
    #[test]
    fn a_real_error_is_reported_ahead_of_an_unused_import() {
        let source = r#"
pub mod Other
  pub fun helper() I64
    return 7
  end
  pub fun spare() I64
    return 9
  end
end

use Other.helper
use Other.spare

pub fun main() I64
  val flag: Bool = helper()
  if flag
    return 1
  end
  return 0
end
"#;
        let errors = errors_for(source);
        assert!(!errors.is_empty(), "{:?}", errors);
        assert!(!errors.iter().any(|m| m.contains("unused import")), "{:?}", errors);
    }

    // A `use` that names a type only mentioned in a signature counts as
    // used: `resolve_type_name` marks the import, so the check must not
    // report an import consumed by anything other than a call.
    #[test]
    fn import_used_only_in_a_type_position_is_accepted() {
        let source = r#"
pub mod Other
  pub type Payload
    pub value: I64
  end
end

use Other.Payload

fun read(payload: &Payload) I64
  return payload.value
end

pub fun main() I64
  val payload = Payload(value: 4)
  return read(&payload)
end
"#;
        let errors = errors_for(source);
        assert!(errors.is_empty(), "{:?}", errors);
    }

    // An import that failed to resolve has already been told what is wrong
    // with it; it must not also be reported as unused.
    #[test]
    fn unresolvable_import_reports_only_the_resolution_failure() {
        let source = r#"
pub mod Other
  pub fun helper() I64
    return 7
  end
end

use Other.missing

pub fun main() I64
  return Other.helper()
end
"#;
        let errors = errors_for(source);
        assert!(errors.iter().any(|m| m.contains("cannot resolve import")), "{:?}", errors);
        assert!(!errors.iter().any(|m| m.contains("unused import")), "{:?}", errors);
    }

    // A `use` of a type that shares its name with a local declaration is a
    // conflict whichever order the two are written in. The import-first
    // order used to be accepted silently, with every later mention of the
    // name resolving to the imported type instead of the local one.
    #[test]
    fn import_before_local_type_of_the_same_name_conflicts() {
        let source = r#"
pub mod Other
  pub type Shape
    pub width: I64
  end
end

use Other.Shape

pub type Shape
  pub height: I64
end

pub fun main() I64
  val shape = Shape(height: 3)
  return shape.height
end
"#;
        let errors = errors_for(source);
        assert!(errors.iter().any(|m| m.contains("import 'Shape' conflicts with another symbol")), "{:?}", errors);
    }

    // The same two declarations in the opposite order, which was already
    // rejected: the diagnostic must be the same one, so that source order
    // decides nothing.
    #[test]
    fn local_type_before_import_of_the_same_name_conflicts() {
        let source = r#"
pub mod Other
  pub type Shape
    pub width: I64
  end
end

pub type Shape
  pub height: I64
end

use Other.Shape

pub fun main() I64
  val shape = Shape(height: 3)
  return shape.height
end
"#;
        let errors = errors_for(source);
        assert!(errors.iter().any(|m| m.contains("import 'Shape' conflicts with another symbol")), "{:?}", errors);
    }

    // The shadowing this rules out, stated as behavior rather than as a
    // diagnostic: with the import written first, `Shape(height: 3)` used to
    // resolve to `Other.Shape` and produce "no field 'height' on struct
    // 'Other.Shape'" — the program was checked against a type its author
    // never named, and the local `Shape` right above it was never reported
    // as conflicting with anything.
    #[test]
    fn import_does_not_silently_shadow_a_later_local_type() {
        let source = r#"
pub mod Other
  pub type Shape
    pub width: I64
  end
end

use Other.Shape

pub type Shape
  pub height: I64
end

pub fun main() I64
  val shape = Shape(height: 3)
  return shape.height
end
"#;
        let errors = errors_for(source);
        assert!(!errors.iter().any(|m| m.contains("Other.Shape")), "{:?}", errors);
    }

    // A local declaration and an import of an unrelated name in the same
    // scope are not a conflict: the placeholder must not be read as
    // occupying every name.
    #[test]
    fn import_beside_an_unrelated_local_type_is_accepted() {
        let source = r#"
pub mod Other
  pub type Shape
    pub width: I64
  end
end

use Other.Shape

pub type Box
  pub height: I64
end

fun widen(shape: &Shape) I64
  return shape.width
end

pub fun main() I64
  val shape = Shape(width: 2)
  val box = Box(height: 3)
  return widen(&shape) + box.height
end
"#;
        let errors = errors_for(source);
        assert!(errors.is_empty(), "{:?}", errors);
    }

    // Enabling the unused-import check newly rejected 27 dead imports across
    // 5 fixtures in the corpus; each was fixed by deleting the dead import
    // (and, where the import was the only thing keeping an otherwise-unused
    // native declaration block reachable — resolve_imports attributes every
    // import edge to ROOT_OWNER regardless of whether it's ever called — by
    // deleting that block too, so removing the import doesn't just trade
    // one diagnostic for a cascade of "unused native function" ones). The
    // fifth, repro/head.cnb, was a language-tour fixture that declared far
    // more surface than its `main` exercised; narrowed to what it actually
    // demonstrates rather than restructuring `main` to call through all of
    // it (a real content decision, made explicitly rather than guessed).
    #[test]
    fn fixture_corpus_stays_clean_of_dead_imports() {
        let paths = [
            "tests/fixtures/repro/mem_probe.cnb",
            "tests/fixtures/repro/slice_test.cnb",
            "tests/fixtures/repro/vec_pop_drain.cnb",
            "tests/fixtures/repro/hash_map_remove_drain.cnb",
            "tests/fixtures/repro/head.cnb",
        ];
        for path in paths {
            let result = crate::analysis::analyze(path, &[]);
            let errors: Vec<String> = result.errors.iter().map(|d| d.0.clone()).collect();
            assert!(errors.is_empty(), "{}: {:?}", path, errors);
        }
    }

    // Pins the fix to resolve_imports never recursing into a module's own
    // child item list: a `use` written inside `mod ... end` used to never
    // resolve at all, no matter how valid the path, because the walk that
    // resolves imports only ever looked at the list it started with.
    #[test]
    fn a_use_inside_a_mod_block_resolves() {
        let source = r#"
pub mod Tools
  pub fun helper() I64
    return 1
  end
end

pub mod Wrapper
  use Tools.helper

  pub fun call_helper() I64
    return helper()
  end
end

pub fun main() I64
  return Wrapper.call_helper()
end
"#;
        let errors = errors_for(source);
        assert!(errors.is_empty(), "{:?}", errors);
    }

    // Negative control: an unresolvable module-local import still reports
    // the resolution failure, not a silent pass -- the recursion above must
    // not accidentally short-circuit resolve_import's own error path.
    #[test]
    fn an_unresolvable_use_inside_a_mod_block_is_rejected() {
        let source = r#"
pub mod Wrapper
  use Tools.nonexistent

  pub fun call_helper() I64
    return 1
  end
end

pub fun main() I64
  return Wrapper.call_helper()
end
"#;
        let errors = errors_for(source);
        assert!(errors.iter().any(|m| m.contains("cannot resolve import")), "{:?}", errors);
    }
}

