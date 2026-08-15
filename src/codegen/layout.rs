//! The `--print-layout` report: sizes, alignments, and field offsets.
//!
//! Covers every concrete struct, enum, and native-handle type the
//! typechecker canonicalized. All numbers come from the exact same lowering
//! a real build uses: the canonical type keys are lowered through
//! `types::llvm_type` and measured with LLVM's target data for the host
//! machine. Field keys reuse `struct_field_keys` (the lowering's own
//! substitution path) and enum variant tags are read from the typechecker's
//! `NODE_VARFACT` rows.
//!
//! `measure_all` lowers each candidate key and returns a `Vec<TypeLayout>`
//! plus the target triple. `render_layouts` formats that vector as aligned
//! text; `layouts_json` formats the same vector as a document. Neither
//! calls `llvm_type` itself.
//!
//! **Invariants:**
//! - Nothing here re-derives a layout fact by parallel logic. A number this
//!   report prints is one the real build would use, or it is not printed —
//!   a layout report that could disagree with the binary would be worse
//!   than none.

use crate::ast::*;
use crate::codegen::error::*;
use crate::codegen::host_target;
use crate::codegen::types::{
    llvm_type, payload_struct_of, struct_field_keys, EnumInfos, KeyTypes, PayloadStructs, TyEnv,
};
use crate::emit_json::LAYOUT_FORMAT;
use crate::typecheck::render_type_key;
use inkwell::context::Context;
use inkwell::types::BasicTypeEnum;
use serde_json::{json, Value};

// The discriminant every enum is lowered with.  Both renderings report it,
// so it is named once here rather than spelled into each of them, where the
// two could drift apart while the emitter moved under both.
const ENUM_TAG_TYPE: &str = "I64";

struct FieldLayout {
    name: i64,
    key: i64,
    offset: u64,
    size: u64,
}

struct VariantLayout {
    name: i64,
    tag: i64,
    payload_size: u64,
}

struct TypeLayout {
    key: i64,
    kind: i64,
    size: u64,
    align: u32,
    payload_offset: i64,
    fields: Vec<FieldLayout>,
    variants: Vec<VariantLayout>,
}

/// Measure every concrete struct/enum/native key in the arena, and report
/// the host triple they were measured for.  Runs after the full front-end;
/// requires no linking tools.
fn measure_all(
    names: &[String],
    nodes: &mut Vec<i64>,
    lists: &mut Vec<Vec<i64>>,
) -> Result<(Vec<TypeLayout>, String), CodegenError> {
    let candidates = collect_candidates(nodes, lists);
    let context = Context::create();
    let (target_data, triple) = host_target()?;
    let mut key_types: KeyTypes = Vec::new();
    let mut enum_infos: EnumInfos = Vec::new();
    let mut payload_structs: PayloadStructs = Vec::new();
    let mut layouts: Vec<TypeLayout> = Vec::new();
    {
        let mut env: TyEnv = (
            &context,
            &target_data,
            names,
            nodes,
            lists,
            &mut key_types,
            &mut enum_infos,
            &mut payload_structs,
        );
        let mut idx = 0usize;
        while idx < candidates.len() {
            let (key, kind) = match candidates.get(idx) {
                Some(pair) => *pair,
                None => break,
            };
            layouts.push(measure_key(&mut env, key, kind)?);
            idx += 1;
        }
    }
    Ok((layouts, triple.as_str().to_string_lossy().to_string()))
}

/// Render the layout report as the aligned text a terminal reads.
pub fn render_layouts(
    names: &[String],
    nodes: &mut Vec<i64>,
    lists: &mut Vec<Vec<i64>>,
) -> Result<String, CodegenError> {
    let (layouts, triple) = measure_all(names, nodes, lists)?;
    let mut out = String::new();
    out.push_str(&format!("# type layouts for {} (sizes and offsets in bytes)\n", triple));
    let mut idx = 0usize;
    while idx < layouts.len() {
        match layouts.get(idx) {
            Some(layout) => render_one(names, nodes, lists, layout, &mut out),
            None => break,
        }
        idx += 1;
    }
    Ok(out)
}

/// Render the same measurement as one JSON document.
///
/// Sizes, alignments, offsets and variant tags are the values `measure_all`
/// produced, so this document and the text report cannot disagree; only the
/// spelling differs.
pub fn layouts_json(
    names: &[String],
    nodes: &mut Vec<i64>,
    lists: &mut Vec<Vec<i64>>,
) -> Result<Value, CodegenError> {
    let (layouts, triple) = measure_all(names, nodes, lists)?;
    let mut types: Vec<Value> = Vec::new();
    let mut idx = 0usize;
    while idx < layouts.len() {
        match layouts.get(idx) {
            Some(layout) => types.push(layout_json(names, nodes, lists, layout)),
            None => break,
        }
        idx += 1;
    }
    Ok(json!({
        "format": LAYOUT_FORMAT,
        "target": triple,
        "types": types
    }))
}

fn layout_json(names: &[String], nodes: &[i64], lists: &[Vec<i64>], layout: &TypeLayout) -> Value {
    let rendered = render_type_key(names, nodes, lists, layout.key);
    if layout.kind == TYD_STRUCT {
        let mut fields: Vec<Value> = Vec::new();
        let mut idx = 0usize;
        while idx < layout.fields.len() {
            match layout.fields.get(idx) {
                Some(field) => fields.push(json!({
                    "name": name_text(names, field.name),
                    "type": render_type_key(names, nodes, lists, field.key),
                    "key": field.key,
                    "offset": field.offset,
                    "size": field.size
                })),
                None => break,
            }
            idx += 1;
        }
        return json!({
            "kind": "struct",
            "type": rendered,
            "key": layout.key,
            "size": layout.size,
            "align": layout.align,
            "fields": fields
        });
    }
    if layout.kind == TYD_ENUM {
        let mut variants: Vec<Value> = Vec::new();
        let mut idx = 0usize;
        while idx < layout.variants.len() {
            match layout.variants.get(idx) {
                Some(variant) => variants.push(json!({
                    "name": name_text(names, variant.name),
                    "tag": variant.tag,
                    "payload_size": variant.payload_size
                })),
                None => break,
            }
            idx += 1;
        }
        // NONE marks an enum lowered to a tag alone; it serializes as null
        // rather than as the sentinel -1.
        let payload_offset = if layout.payload_offset == NONE {
            Value::Null
        } else {
            json!(layout.payload_offset)
        };
        return json!({
            "kind": "enum",
            "type": rendered,
            "key": layout.key,
            "size": layout.size,
            "align": layout.align,
            "tag_type": ENUM_TAG_TYPE,
            "payload_offset": payload_offset,
            "variants": variants
        });
    }
    json!({
        "kind": "native",
        "type": rendered,
        "key": layout.key,
        "size": layout.size,
        "align": layout.align,
        "opaque": true
    })
}

// Concrete struct/enum/native keys, in canonical key order.  A key
// containing a type parameter (or an unknown/mono marker) has no machine
// layout and is skipped.
fn collect_candidates(nodes: &[i64], lists: &[Vec<i64>]) -> Vec<(i64, i64)> {
    let mut out: Vec<(i64, i64)> = Vec::new();
    let count = nodes.len() as i64 / NODE_STRIDE;
    let mut id = 0i64;
    while id < count {
        if node_tag(nodes, id) == NODE_TYINFO {
            let key = node_a(nodes, id);
            let kind = node_b(nodes, id);
            if (kind == TYD_STRUCT || kind == TYD_ENUM || kind == TYD_NATIVE)
                && key_is_concrete(nodes, lists, key)
            {
                out.push((key, kind));
            }
        }
        id += 1;
    }
    out
}

fn key_is_concrete(nodes: &[i64], lists: &[Vec<i64>], key: i64) -> bool {
    if key < 0 {
        return false;
    }
    let row = find_tyinfo(nodes, key);
    if row == NONE {
        return false;
    }
    let kind = node_b(nodes, row);
    if kind == TYD_PARAM || kind == TYD_UNKNOWN || kind == TYD_MONO {
        return false;
    }
    let args = node_d(nodes, row);
    let nargs = list_len(lists, args);
    let mut idx = 0i64;
    while idx < nargs {
        if !key_is_concrete(nodes, lists, list_get(lists, args, idx)) {
            return false;
        }
        idx += 1;
    }
    let elem = node_e(nodes, row);
    if elem != NONE && !key_is_concrete(nodes, lists, elem) {
        return false;
    }
    true
}

fn span_of_key(nodes: &[i64], key: i64) -> (i64, i64, i64) {
    let row = find_tyinfo(nodes, key);
    if row == NONE {
        return (NO_FILE, 0, 0);
    }
    let sym = node_c(nodes, row);
    let item = node_c(nodes, sym);
    if item == NONE {
        return (NO_FILE, 0, 0);
    }
    (node_file(nodes, item), node_start(nodes, item), node_end(nodes, item))
}

fn measure_key(env: &mut TyEnv, key: i64, kind: i64) -> Result<TypeLayout, CodegenError> {
    let span = span_of_key(env.3, key);
    let ty = llvm_type(env, key, span)?;
    let size = env.1.get_abi_size(&ty);
    let align = env.1.get_abi_alignment(&ty);
    if kind == TYD_STRUCT {
        return measure_struct(env, key, ty, size, align, span);
    }
    if kind == TYD_ENUM {
        return measure_enum(env, key, ty, size, align, span);
    }
    Ok(TypeLayout {
        key,
        kind,
        size,
        align,
        payload_offset: NONE,
        fields: Vec::new(),
        variants: Vec::new(),
    })
}

fn measure_struct(
    env: &mut TyEnv,
    key: i64,
    ty: BasicTypeEnum,
    size: u64,
    align: u32,
    span: (i64, i64, i64),
) -> Result<TypeLayout, CodegenError> {
    let row = find_tyinfo(env.3, key);
    let sym = node_c(env.3, row);
    let item = node_c(env.3, sym);
    let args = node_d(env.3, row);
    let field_keys = struct_field_keys(env.3, env.4, item, args);
    let struct_ty = match ty {
        BasicTypeEnum::StructType(st) => st,
        BasicTypeEnum::ArrayType(other) => {
            return Err(builder_error(span.0, span.1, span.2, &format!("struct key {} lowered to non-struct type {:?}", key, other)));
        }
        BasicTypeEnum::FloatType(other) => {
            return Err(builder_error(span.0, span.1, span.2, &format!("struct key {} lowered to non-struct type {:?}", key, other)));
        }
        BasicTypeEnum::IntType(other) => {
            return Err(builder_error(span.0, span.1, span.2, &format!("struct key {} lowered to non-struct type {:?}", key, other)));
        }
        BasicTypeEnum::PointerType(other) => {
            return Err(builder_error(span.0, span.1, span.2, &format!("struct key {} lowered to non-struct type {:?}", key, other)));
        }
        BasicTypeEnum::VectorType(other) => {
            return Err(builder_error(span.0, span.1, span.2, &format!("struct key {} lowered to non-struct type {:?}", key, other)));
        }
        BasicTypeEnum::ScalableVectorType(other) => {
            return Err(builder_error(span.0, span.1, span.2, &format!("struct key {} lowered to non-struct type {:?}", key, other)));
        }
    };
    let mut fields: Vec<FieldLayout> = Vec::new();
    let mut idx = 0usize;
    while idx < field_keys.len() {
        let (fname, fkey) = match field_keys.get(idx) {
            Some(pair) => *pair,
            None => break,
        };
        let offset = match env.1.offset_of_element(&struct_ty, idx as u32) {
            Some(value) => value,
            None => {
                return Err(builder_error(
                    span.0,
                    span.1,
                    span.2,
                    &format!("no element offset for field index {} of struct key {}", idx, key),
                ));
            }
        };
        let field_ty = llvm_type(env, fkey, span)?;
        let field_size = env.1.get_abi_size(&field_ty);
        fields.push(FieldLayout { name: fname, key: fkey, offset, size: field_size });
        idx += 1;
    }
    Ok(TypeLayout { key, kind: TYD_STRUCT, size, align, payload_offset: NONE, fields, variants: Vec::new() })
}

fn measure_enum(
    env: &mut TyEnv,
    key: i64,
    ty: BasicTypeEnum,
    size: u64,
    align: u32,
    span: (i64, i64, i64),
) -> Result<TypeLayout, CodegenError> {
    let row = find_tyinfo(env.3, key);
    let sym = node_c(env.3, row);
    let item = node_c(env.3, sym);
    let variants_list = node_e(env.3, item);
    let count = list_len(env.4, variants_list);
    let payload_offset = match ty {
        BasicTypeEnum::StructType(st) => {
            if st.count_fields() > 1 {
                match env.1.offset_of_element(&st, 1) {
                    Some(value) => value as i64,
                    None => NONE,
                }
            } else {
                NONE
            }
        }
        BasicTypeEnum::ArrayType(other) => {
            return Err(builder_error(span.0, span.1, span.2, &format!("enum key {} lowered to non-struct type {:?}", key, other)));
        }
        BasicTypeEnum::FloatType(other) => {
            return Err(builder_error(span.0, span.1, span.2, &format!("enum key {} lowered to non-struct type {:?}", key, other)));
        }
        BasicTypeEnum::IntType(other) => {
            return Err(builder_error(span.0, span.1, span.2, &format!("enum key {} lowered to non-struct type {:?}", key, other)));
        }
        BasicTypeEnum::PointerType(other) => {
            return Err(builder_error(span.0, span.1, span.2, &format!("enum key {} lowered to non-struct type {:?}", key, other)));
        }
        BasicTypeEnum::VectorType(other) => {
            return Err(builder_error(span.0, span.1, span.2, &format!("enum key {} lowered to non-struct type {:?}", key, other)));
        }
        BasicTypeEnum::ScalableVectorType(other) => {
            return Err(builder_error(span.0, span.1, span.2, &format!("enum key {} lowered to non-struct type {:?}", key, other)));
        }
    };
    let mut variants: Vec<VariantLayout> = Vec::new();
    let mut idx = 0i64;
    while idx < count {
        let variant = list_get(env.4, variants_list, idx);
        let vname = node_a(env.3, variant);
        // The declared-order tag is the typechecker's attached fact; NONE
        // means the fact row was never created (an unreferenced builtin
        // instantiation), in which case the variant list's declared order
        // is the same single fact read from the tree it was derived from.
        let fact_tag = varfact_index_of(env.3, key, vname);
        let tag = if fact_tag == NONE { idx } else { fact_tag };
        let payload_ty = payload_struct_of(env, key, idx, span)?;
        let payload_size = env.1.get_abi_size(&payload_ty);
        variants.push(VariantLayout { name: vname, tag, payload_size });
        idx += 1;
    }
    Ok(TypeLayout { key, kind: TYD_ENUM, size, align, payload_offset, fields: Vec::new(), variants })
}

fn render_one(names: &[String], nodes: &[i64], lists: &[Vec<i64>], layout: &TypeLayout, out: &mut String) {
    let rendered = render_type_key(names, nodes, lists, layout.key);
    if layout.kind == TYD_STRUCT {
        out.push_str(&format!("struct {}  size={} align={}\n", rendered, layout.size, layout.align));
        let mut idx = 0usize;
        while idx < layout.fields.len() {
            match layout.fields.get(idx) {
                Some(field) => out.push_str(&format!(
                    "  {}: {}  offset={} size={}\n",
                    name_text(names, field.name),
                    render_type_key(names, nodes, lists, field.key),
                    field.offset,
                    field.size
                )),
                None => break,
            }
            idx += 1;
        }
        return;
    }
    if layout.kind == TYD_ENUM {
        if layout.payload_offset == NONE {
            out.push_str(&format!(
                "enum {}  size={} align={}  tag={} (no payload)\n",
                rendered, layout.size, layout.align, ENUM_TAG_TYPE
            ));
        } else {
            out.push_str(&format!(
                "enum {}  size={} align={}  tag={} payload-offset={}\n",
                rendered, layout.size, layout.align, ENUM_TAG_TYPE, layout.payload_offset
            ));
        }
        let mut idx = 0usize;
        while idx < layout.variants.len() {
            match layout.variants.get(idx) {
                Some(variant) => out.push_str(&format!(
                    "  {}  tag={} payload-size={}\n",
                    name_text(names, variant.name),
                    variant.tag,
                    variant.payload_size
                )),
                None => break,
            }
            idx += 1;
        }
        return;
    }
    out.push_str(&format!(
        "native {}  size={} align={}  (opaque handle)\n",
        rendered, layout.size, layout.align
    ));
}
