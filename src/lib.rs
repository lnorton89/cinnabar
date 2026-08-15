//! The Cinnabar compiler pipeline, exposed as a library.
//!
//! The CLI driver (`src/main.rs`) and the language server
//! (`src/bin/cinnabar_lsp.rs`) consume one shared implementation of every
//! stage through this crate. The pipeline is not altered by being a
//! library: each stage computes its facts once and attaches them to the
//! flat node arena for every later consumer to read.
//!
//! **Invariants:**
//! - There is exactly one implementation of each stage. A second entry
//!   point that re-ran resolution or inference for tooling's convenience
//!   would be the Single-Fact Rule broken at the largest available scale —
//!   an editor and a build disagreeing about the same program.

pub mod analysis;
pub mod advanced_tools;
pub mod ast;
pub mod borrow;
#[cfg(feature = "codegen")]
pub mod codegen;
pub mod docs;
pub mod emit_json;
pub mod format;
pub mod inspect;
pub mod lexer;
pub mod module_loader;
pub mod native_stub;
pub mod parser;
pub mod project;
pub mod resolver;
pub mod suggest;
pub mod typecheck;
