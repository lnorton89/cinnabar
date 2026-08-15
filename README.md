# Cinnabar

[![CI](https://github.com/bonzupii/cinnabar/actions/workflows/ci.yml/badge.svg)](https://github.com/bonzupii/cinnabar/actions/workflows/ci.yml)
[![OpenSSF Scorecard](https://api.scorecard.dev/projects/github.com/bonzupii/cinnabar/badge)](https://scorecard.dev/viewer/?uri=github.com/bonzupii/cinnabar)

Cinnabar is a **zero-trust systems language for durable software**. It assumes that code authors may optimize for immediate task completion rather than long-term correctness, whether they are humans under pressure or AI code-generating systems. Cinnabar therefore grants no mechanism to bypass, suppress, weaken, or defer its safety, ownership, failure-handling, and explicitness invariants. Programs must express valid designs within those invariants; designs that require an exception are not representable in Cinnabar.

Concretely, it is a from-scratch, statically-typed compiler written in Rust, targeting native machine code via LLVM, for building compilers, runtimes, kernels, firmware, and network stacks — domains where garbage collection, hidden control flow, and runtime panics are unacceptable.

There is no `#[allow]`, no warning severity, no suppression pragma, and no escape hatch to add one. If you are looking for the flag that turns a check off, its absence is the feature.

The language's defining feature is **Austral-style linear typing**: resource-owning handles (heap memory, vectors, strings, hash maps, sockets) must be consumed exactly once on every execution path, enforced entirely at compile time by a dedicated flow-sensitive borrow checker — with no lifetime annotations, no garbage collector, and no reference counting.

> The authoritative language specification is [`MANIFESTO.md`](MANIFESTO.md). If anything below (or any `.cnb` file in the repo) contradicts it, the manifesto wins.

## Language highlights

- **Linear resource management.** Native handles (`Memory.Block`, `Collections.Vec(T)`, `Collections.String`, `Collections.HashMap(K, V)`) must be consumed exactly once on every path — no double-free, no use-after-move, no leaks, checked statically.
- **No lifetime annotations.** Borrow scopes are flow-sensitive and inferred by the compiler; an ambiguous returned borrow is a compile error, resolved by restructuring the API, not by annotating.
- **No dereference operator.** There is no `*` or `->`. References are accessed through field access, method calls, and pattern matching; the compiler manages indirection internally.
- **Errors only, never warnings.** There is no lint severity, no `#[allow]`. A program either compiles cleanly or is rejected with a real diagnostic.
- **No panics reachable from user code.** Division, modulo, and dynamic indexing return `Result` instead of trapping. Constant-provable zero-division and out-of-range constant indices are compile-time errors instead.
- **O(1) call-stack recursion.** Every self-recursive call must be in strict tail position (a compile-time-enforced rule); LLVM tail-call elimination turns it into a jump, so there is no runtime stack guard and no stack-overflow crash.
- **Explicit everything.** `val`/`var` (immutable/mutable), `pub` (visibility), `impure` (side effects/effect purity), `try` (Result/Option propagation), and casing itself (`snake_case`/`PascalCase`/`SCREAMING_SNAKE_CASE`) are all compiler-enforced grammar, not convention.
- **Static, freestanding binaries.** The compiler links every program statically against a staged musl libc — no dynamic linker dependency in the output binary.

See [`MANIFESTO.md`](MANIFESTO.md) for the full, normative specification and the full list of anti-principles (no macros, no operator overloading, no async, no trait objects, no GC, no exceptions).

## A taste of the language

Every snippet below is copied verbatim from the repository's own known-good fixture corpus in [`tests/fixtures/`](tests/fixtures/) — each is a complete, compiling program with a real `main`, not hand-assembled for this document. (This repo's toolchain requires LLVM 21 + a staged musl libc via `nix develop`, which isn't available in the environment these docs were written in, so "known-good, taken from the fixture corpus" stands in for "compiled and verified locally.")

Tail recursion and structs — [`tests/fixtures/repro/hanoi.cnb`](tests/fixtures/repro/hanoi.cnb):

```cinnabar
pub const DISKS: I64 = 8

pub type MoveCount
  pub moves: I64
end

fun hanoi_acc(n: I64, acc: I64) I64
  if n <= 0
    return acc
  end
  return hanoi_acc(n - 1, acc + acc + 1)
end

fun hanoi_moves(disks: I64) I64
  return hanoi_acc(disks, 0)
end

fun hanoi(n: I64) MoveCount
  return MoveCount(moves: hanoi_moves(n))
end

pub fun main() I64
  val result = hanoi(DISKS)
  return result.moves
end
```

Linear native handles, generics, and `Result` — [`tests/fixtures/repro/vec_test.cnb`](tests/fixtures/repro/vec_test.cnb):

```cinnabar
pub mod Collections
  pub nat type Vec(T)
  pub nat type String
  pub nat type HashMap(K, V)

  pub type Error
    pub AllocationFailed(Usize)
    pub IndexOutOfBounds(Usize)
    pub KeyNotFound
    pub EmptySlice
    pub InvalidUtf8
  end

  pub nat fun vec_new<T>() impure Result(Vec(T), Error)
  pub nat fun vec_push<T>(vec: &mut Vec(T), value: T) impure Result(Unit, Error)
  pub nat fun vec_view<T>(vec: &Vec(T)) &[T]
  pub nat fun vec_free<T>(vec: Vec(T)) impure Unit
  pub nat fun string_from_slice(view: &[U8]) impure Result(String, Error)
  pub nat fun string_len(value: &String) Usize
  pub nat fun string_free(value: String) impure Unit
  pub nat fun hash_map_new<K, V>() impure Result(HashMap(K, V), Error)
  pub nat fun hash_map_insert<K, V>(map: &mut HashMap(K, V), key: K, value: V) impure Result(Unit, Error)
  pub nat fun hash_map_get<K, V>(map: &HashMap(K, V), key: K) impure Result(V, Error)
  pub nat fun hash_map_free<K, V>(map: HashMap(K, V)) impure Unit
end

use Collections.vec_new
use Collections.vec_push
use Collections.vec_view
use Collections.vec_free

pub mod Slice
  pub nat fun len<T>(view: &[T]) Usize
end

use Slice.len as slice_len

const BAD_NEW: I64 = 1
const BAD_PUSH: I64 = 2

fun fail_vec<T>(vec: Collections.Vec(T)) impure I64
  vec_free(vec)
  return BAD_PUSH
end

fun fill_squares(vec: &mut Collections.Vec(I64)) impure Result(Unit, Collections.Error)
  var i: I64 = 0
  while i < 5
    try vec_push(vec, i * i)
    i = i + 1
  end
  return Ok(Unit)
end

pub fun main() impure I64
  val vec = match vec_new[I64]()
    Ok(v) => v
    Err(error) => return BAD_NEW
  end

  val fill_result = fill_squares(&mut vec)
  match fill_result
    Ok(Unit) => Unit
    Err(error) => return fail_vec(vec)
  end

  val view = vec_view(&vec)
  val n = slice_len(view)
  vec_free(vec)          # linear handle consumed exactly once
  return 0
end
```

Slices, array rest-patterns, and tail-recursive folds — [`tests/fixtures/repro/slice_test.cnb`](tests/fixtures/repro/slice_test.cnb):

```cinnabar
fun slice_sum_acc(view: &[U8], acc: Usize) Usize
  match view
    [] => return acc
    [first, rest @ ..] => return slice_sum_acc(rest, acc + Usize.from(first))
  end
end

fun slice_sum(view: &[U8]) Usize
  return slice_sum_acc(view, 0)
end

pub const MAGIC_BYTE_0: U8 = 0x0D
pub const MAGIC_BYTE_1: U8 = 0xF0
pub const MAGIC_BYTE_2: U8 = 0xAD
pub const MAGIC_BYTE_3: U8 = 0x0B
pub const EXPECTED_SUM: Usize = 437

fun array_as_slice() Usize
  val bytes: [U8; 4] = [MAGIC_BYTE_0, MAGIC_BYTE_1, MAGIC_BYTE_2, MAGIC_BYTE_3]
  return slice_sum(&bytes)
end

pub fun main() I64
  if array_as_slice() == EXPECTED_SUM
    return 0
  end
  return 1
end
```

Multi-file modules, resolved automatically from `use` statements — [`tests/fixtures/multi_file/`](tests/fixtures/multi_file/), where `use Math.add` in `main.cnb` loads the sibling file `Math.cnb`:

```cinnabar
# main.cnb
use Math.add

pub fun main() I64
  return add(10, 20)
end
```

```cinnabar
# Math.cnb
pub fun add(a: I64, b: I64) I64
  return a + b
end
```

More real examples live in [`tests/fixtures/`](tests/fixtures/), especially [`tests/fixtures/spec.cnb`](tests/fixtures/spec.cnb) — the immutable reference implementation fixture, which doubles as an executable language tour (traits, `impl`, checksum-style dispatch, and more).

## Building the compiler

Cinnabar targets **LLVM 21** (via the `inkwell` crate) and requires `clang`/`llc`/`opt` on `PATH`. Static `--static` builds on Linux self-provision musl from upstream at build time (see `build.rs`). The project ships a Nix flake that provisions the LLVM toolchain:

```bash
nix develop
cargo build --release
```

Outside of `nix develop`, `cargo build`/`cargo clippy` will fail unless you have a matching LLVM 21 toolchain and `clang` on `PATH`. `build.rs` self-provisions musl from upstream for static builds (via `curl`/`wget`, `tar`, `make`, and `sha256sum`), so no host musl package is required; `MUSL_LIBC_A` remains available as a manual override. See [`build.rs`](build.rs) and [`flake.nix`](flake.nix) for the exact discovery logic and paths.

### Docker Desktop and Windows worktrees

Windows contributors can run the same Nix environment in one reusable Docker Compose service. Its named Nix and Cargo caches survive branch changes, while every worktree receives an isolated Rust `target` volume. The setup also includes the linked-worktree Git mounts needed by Nix and a rust-analyzer wrapper that runs inside `nix develop`.

See [`CONTAINER_DEVELOPMENT.md`](CONTAINER_DEVELOPMENT.md) for setup, VS Code attachment, worktree switching, and verification commands. Native Linux development remains Nix-first and does not require Docker.

## Using the compiler

There are two ways to invoke `cinnabar`. Given a **source file**, it runs the whole pipeline and
writes a static binary. Given a **subcommand**, it acts on the project whose `build.cnb` manifest is
discovered by walking upward from the supplied path.

```
cinnabar <FILE> [-o|--output PATH] [--dump-ast] [--dump-typed-ast] [--print-layout]
                [--emit-llvm] [--emit-obj] [--explain-borrow[=human|json]] [--emit-json]
                [--run] [-O|--opt-level {0,1,2,3,s,z}]
cinnabar <COMMAND> [ARGS]
```

Every command below is documented in the binary itself — `cinnabar <COMMAND> --help` prints the
full description, not a one-line summary.

### Compiling a single file

| Flag | Description |
|---|---|
| `<FILE>` | Input Cinnabar source file (positional, required), conventionally `.cnb` |
| `-o, --output <PATH>` | Output binary path (defaults to the input path with `.cnb` stripped) |
| `--dump-ast` | Parse only, pretty-print the AST, and exit (no resolve/typecheck/borrow-check/codegen) |
| `--dump-typed-ast` | Run the full front-end, then print the node arena with every attached fact (resolved symbols, canonical type keys, linearity flags, variant tags, field facts) and exit |
| `--print-layout` | Run the full front-end, then print ABI size, alignment, field offsets, and enum variant tags for every concrete struct/enum/native handle and exit |
| `--emit-llvm` | Write the emitter's LLVM IR (before optimization) to the input path with `.ll` and stop |
| `--emit-obj` | Optimize and assemble to a relocatable object at the input path with `.o`, skipping the static link |
| `--explain-borrow[=human\|json]` | Attach secondary labels to borrow/linearity errors: which paths consume a value, where it was bound (and its linear type), where it was previously moved. `=json` emits them as structured diagnostics instead |
| `--emit-json` | Write the invocation's result to standard output as one JSON document instead of terminal text — see [Machine-readable output](#machine-readable-output). Cannot be combined with `--run`, which gives the program's own output the same stream |
| `--run` | Execute the produced binary after a successful build; `cinnabar` then exits `0` if the program exited `0` and non-zero otherwise |
| `-O, --opt-level <LEVEL>` | LLVM optimization level: `0`, `1`, `2`, `3`, `s`, `z` (default `2`) |

```bash
cargo run -- tests/fixtures/spec.cnb                  # compiles spec.cnb -> tests/fixtures/spec
cargo run -- tests/fixtures/multi_file/main.cnb --run # compiles and runs, following `use Math.add`
cargo run -- my_program.cnb --dump-ast                # inspect the parsed AST
```

On success the compiler prints `Successfully compiled <input> to '<output>'.` and exits `0`. Any
lex, parse, resolve, typecheck, borrow-check, or codegen failure is rendered as one or more
source-located diagnostics (via [`ariadne`](https://github.com/zesterer/ariadne)) and exits
non-zero. There is no partial output: a build either produces its artifact or produces diagnostics.

### Machine-readable output

Every introspection surface above was written for a terminal. `--emit-json` writes the same facts
to standard output as **exactly one JSON document per invocation**, so an editor, a playground, or
a snapshot reviewer can consume them without scraping formatted text.

| Invocation | Document |
|---|---|
| `<FILE> --dump-ast --emit-json` | `cinnabar.ast.v1` — the node arena as parsing left it |
| `<FILE> --dump-typed-ast --emit-json` | `cinnabar.typed-ast.v1` — the same arena with every front-end attachment filled in |
| `<FILE> --print-layout --emit-json` | `cinnabar.layout.v1` — sizes, alignments, field offsets, enum variant tags |
| any other invocation with `--emit-json` | `cinnabar.diagnostics.v1` — every diagnostic the run produced, **empty when the program was accepted** |

Each document names its shape in a `format` field, which is what a consumer should branch on.

```bash
cinnabar main.cnb --check-only --emit-json     # {"format":"cinnabar.diagnostics.v1","diagnostics":[]}
cinnabar main.cnb --dump-typed-ast --emit-json | jq '.nodes[] | select(.tag == "EXPR")'
cinnabar main.cnb --print-layout --emit-json   | jq '.types[] | select(.kind == "struct")'
```

**The arena documents** (`ast` / `typed-ast`) carry `names` (the interning table), `lists` (the list
arena), `root` (the index into `lists` of the top-level item list), and `nodes`. Each node reports
its `id`, symbolic `tag`, raw `file`/`start`/`end`/`slots`, and a `detail` object naming what the
row means — the resolved symbol, the canonical type key with its rendering, the variant tag, the
field offset fact. The two documents have the same shape and differ only in which attachment slots
are still `-1`.

**Spans.** A row or diagnostic with a real source origin carries a `source` object with byte
offsets *and* the line/UTF-16-column pair the language server computes from the same mapping, so an
editor and a `--emit-json` consumer cannot disagree about where something points. A fact with no
Cinnabar source origin — an internal failure, a linker error, a type-descriptor row whose leading
slots hold linearity flags rather than a span — reports `"source": null` rather than a plausible
location. Nothing here invents a position; see the "Honest Diagnostics" goal in
[`MANIFESTO.md`](MANIFESTO.md).

**The diagnostic envelope** carries, per diagnostic, its `severity`, `message`, `source`, and
`explanations` — the same secondary labels `--explain-borrow` renders in a terminal, including the
borrow checker's consume paths, binding sites, and prior move sites. `--explain-borrow=json`
remains as the older spelling of that request and now emits this same envelope.

`--emit-json` applies to the single-file invocation form. It cannot be combined with `--run`, since
the executed program writes to the same stream the document would.

### Working on a project

| Command | What it does |
|---|---|
| `cinnabar init [PATH]` | Scaffold `build.cnb`, `main.cnb`, and `tests/smoke.cnb`. Refuses to overwrite: if any of the three exists, it writes none of them |
| `cinnabar build [PATH] [--target host]` | Compile the manifest's `ENTRY` to `<project>/target/<NAME>` |
| `cinnabar run [PATH] [--target host]` | Build, then execute the artifact. Exits `0` if the program exited `0`, non-zero otherwise |
| `cinnabar check [PATH]` | Load, resolve, typecheck, and borrow-check; stop before code generation. Needs no LLVM and links nothing |
| `cinnabar test [PATH] [--update-snapshots]` | Compile and run every `.cnb` file under the manifest's `TESTS` directory, recursively |
| `cinnabar fmt [--check] <FILE>` | Rewrite one file into canonical form, or (with `--check`) exit non-zero if it isn't already |
| `cinnabar doc [PATH] [-o DIR] [--emit-json]` | Render every public declaration into `<project>/target/doc/index.html`, or with `--emit-json` write it as a `cinnabar.docs.v1` document for a documentation site to lay out itself |
| `cinnabar snapshots [PATH] [--address ADDR] [--emit-json]` | Review diagnostic snapshot changes one fixture at a time, on a loopback page. Accepting writes that one `.stderr` sidecar; `test --update-snapshots` accepts all of them at once |
| `cinnabar burn [PATH] [--address ADDR]` | Serve those docs plus the manifesto over HTTP, pinned to this compiler's version (default `127.0.0.1:7878`) |

`PATH` defaults to `.` and may be a project directory, a `build.cnb`, or a source path inside the
project — the manifest is found by walking upward from it either way. `--target` currently accepts
only `host`; run `cinnabar targets` for the list and the state of each.

`check` is not a laxer `build`. It runs the same stages `build` runs and reaches the same verdicts;
it stops once the front end has established everything it can establish without emitting code.

`build` and `run` name the artifact after the manifest's `NAME` field rather than after whichever
file happens to be `ENTRY` — a project that renames its entry source has not renamed itself.

#### The manifest

`build.cnb` is Cinnabar source, not a configuration format. It is read back through the compiler's
own front end, so it obeys the same casing, typing, and literal rules as any other program — and a
mistake in it is reported as an ordinary diagnostic pointing at the offending line:

```cinnabar
pub const NAME: &[U8] = "my_project"
pub const ENTRY: &[U8] = "main.cnb"
pub const TESTS: &[U8] = "tests"
```

`NAME` names the built artifact and must be a single path component. `ENTRY` and `TESTS` are
relative paths confined to the project root. `TESTS` may be omitted, and then defaults to `tests`.

#### Test layout

`cinnabar test` decides what is expected of a file from its name:

| File | Expectation |
|---|---|
| `case.cnb` | Must compile, link, and exit `0` |
| `case.cnb.exit` | The non-zero status `case.cnb` is expected to exit with |
| `case.reject.cnb` | Must be *rejected*; compiling it successfully is a failure |
| `case.reject.cnb.stderr` | The exact diagnostic that rejection must produce |

A `.stderr` sidecar makes its test a rejection test whether or not the name says `.reject`, and the
snapshot is compared in full rather than searched for a substring — a diagnostic is part of what the
compiler promises, so a change to its wording is a change to be reviewed. `--update-snapshots`
rewrites those sidecars from what the compiler currently prints; it is for deliberately accepting a
diagnostic whose diff you have read, not for making a red run go green.

### Inspecting and experimenting

| Command | What it does |
|---|---|
| `cinnabar targets` | List code-generation targets and whether this binary can build for each |
| `cinnabar inspect [PATH] [-o FILE]` | Build, then report computed layouts alongside the linked binary's sections, symbols, and disassembly |
| `cinnabar soundness [PATH] [-o FILE]` | Emit what the front end established as JSON. Evidence, not a proof — the report says `formal_proof: false` and scopes itself |
| `cinnabar playground [--address ADDR]` | Serve a local page that compiles and runs submitted source. Loopback-only, size-capped, and time-limited by design (default `127.0.0.1:7879`) |
| `cinnabar mushlings {init\|verify} [PATH]` | Exercises that teach the language through its own diagnostics; the real compiler decides whether a fix is right |
| `cinnabar fuzz replay <FILE>` | Recompile a saved fuzz artifact and report whether it still reproduces its failure |
| `cinnabar fuzz minimize <FILE> [-o FILE]` | Shrink an artifact to the smallest source with the *same* failure signature |
| `cinnabar native-stub <IDL> -o <FILE>` | Generate a typed, opaque `nat type`/`nat fun` surface from the constrained native IDL |

## Language server

The repository also builds `cinnabar-lsp`, a Language Server Protocol server over the same compiler pipeline:

```bash
cargo build --release --bin cinnabar-lsp
```

It speaks stdio and provides diagnostics (with the borrow checker's explanatory notes as related information and code lenses), hover (attached types and signatures, linearity), go-to-definition and find-references across the module graph, completion (resolver-visible symbols and `use` paths, lexically scoped locals, struct fields after `.`, enum variants, keywords), and signature help. Full front-end checks are debounced after edits and run off the protocol loop; generation checks prevent superseded results from being published. Point any LSP client at the binary for `.cnb` files — e.g. in VS Code via a generic LSP extension, or in Neovim:

```lua
vim.lsp.start({ name = "cinnabar", cmd = { "/path/to/cinnabar-lsp" }, root_dir = vim.fn.getcwd() })
```

Every answer is read from the facts the pipeline attaches (resolved symbol ids, canonical type keys); the server contains no second implementation of name resolution or type inference.

## Compiler architecture

Cinnabar is a single fixed pipeline:

```
lexer → parser → module_loader → resolver → typechecker → borrow_checker → codegen
```

Every stage computes its facts exactly once and attaches them to the program representation for later stages to read — nothing is silently re-derived downstream. See [`ARCHITECTURE.md`](ARCHITECTURE.md) for a full technical walkthrough of each stage, the compiler's unusual flat-array/arena internal representation, and the codegen/linking pipeline.

## Repository layout

```
src/
  lib.rs            Library crate exposing the pipeline to the CLI and tooling
  main.rs           CLI driver, pipeline wiring, AST dumper
  bin/cinnabar_lsp.rs  Language server (JSON-RPC shell over analysis.rs)
  lexer.rs          Hand-written byte-level lexer
  parser.rs         Recursive-descent parser
  ast.rs            Flat node-arena AST representation and opcode constants
  module_loader.rs  Multi-file module discovery/loading (with editor-buffer overlay)
  resolver.rs       Name resolution, scoping, casing enforcement
  typecheck.rs      Type checking, canonical type keys, linearity inference
  borrow.rs         Flow-sensitive borrow/linearity checker (CFG dataflow, explainer notes)
  analysis.rs       IDE queries over attached facts (hover, definition, references, ...)
  docs.rs           Attached-doc HTML generation and local Cinnabook server
  project.rs        build.cnb discovery, initialization, tests, and snapshots
  inspect.rs        --dump-typed-ast arena serialization
  codegen/          LLVM IR generation (via inkwell), layout report, native linking
tests/
  fixtures/         .cnb example/regression programs (positive and EXPECT_REJECTED)
austral_refs/       Reference material from Austral (the language's direct influence)
MANIFESTO.md        Normative language specification
ROADMAP.md          Planned milestones and open work
AGENTS.md           Contribution/AI-agent working conventions for this repo
pre_commit_check.sh Build/lint/test/fixture verification gate
flake.nix           Nix dev shell (LLVM, clang, valgrind, etc.)
build.rs            Locates and stages a static musl libc for linking
```

## Verifying a change

The repository's build gate is [`pre_commit_check.sh`](pre_commit_check.sh), run inside the Nix dev shell:

```bash
nix develop --command ./pre_commit_check.sh
```

It runs `cargo check`, `cargo clippy -D warnings`, a custom Semgrep ruleset, `cargo test`, CLI smoke checks, compiles and `--dump-ast`s several fixtures, runs the compiled `spec.cnb` reference binary, and runs a battery of `EXPECT_REJECTED` negative fixtures (bad casing, immutable assignment, unknown variables, nested comments, etc.). See [`AGENTS.md`](AGENTS.md) for the full set of repository conventions this project holds itself to (no `unwrap`/`panic!`, no `_` discard bindings, no re-derived facts, category-level fixes only, etc.).

### Faster local test profiles

The default `full` profile preserves exhaustive gate coverage. For quicker local feedback, `balanced` and `smoke` reduce the randomized corpus sizes and the number of successful fixtures that are linked and executed. Successful cases not selected for execution still pass through parsing, resolution, typechecking, borrow checking, code generation, and LLVM IR emission; the reduced profiles mainly avoid repeated `llc` and static-link work. Rejected fixtures remain checked.

| Profile | Fuzz corpus | Native fuzz runs | Native expected-fixture runs | Record-only runs |
| --- | ---: | ---: | ---: | ---: |
| `full` | 80 valid + 80 invalid | all 80 valid cases | all | all |
| `balanced` | 32 valid + 32 invalid | 8 | 10 | 2 |
| `smoke` | 8 valid + 8 invalid | 2 | 4 | 0 |

```bash
# Full coverage (the default)
nix develop --command cargo test --quiet

# Routine local iteration
nix develop --command cargo test --quiet --features test-profile-balanced

# Fastest structural feedback
nix develop --command cargo test --quiet --features test-profile-smoke
```

Individual budgets can be overridden when a reduced profile is still broader or narrower than needed. The full profile ignores these variables, so an exported local override cannot silently reduce `pre_commit_check.sh` coverage:

| Environment variable | Controls |
| --- | --- |
| `CINNABAR_FUZZ_POSITIVE_CASES` | Generated valid programs compiled |
| `CINNABAR_FUZZ_NEGATIVE_CASES` | Generated invalid linearity programs rejected |
| `CINNABAR_FUZZ_RUN_CASES` | Valid fuzz programs additionally linked and executed |
| `CINNABAR_REPRO_RUN_CASES` | Expected-success fixtures additionally linked and executed |
| `CINNABAR_REPRO_RECORD_CASES` | Record-only fixtures compiled and run |
| `CINNABAR_REPRO_LINK_COMPILE_ONLY` | Whether blocking compile-only fixtures are linked (`true`) instead of stopping at LLVM IR (`false`) |
| `CINNABAR_TEST_RUN_TIMEOUT_SECS` | Per-program execution timeout |
| `CINNABAR_TEST_COMPILE_TIMEOUT_SECS` | Per-program fuzz compilation timeout |

Case budgets use an even sample across each ordered corpus instead of taking only its first entries. These controls are intended for local iteration; run `nix develop --command ./pre_commit_check.sh` with no profile override before submitting a change.

## Status

Cinnabar is under active early development. See [`ROADMAP.md`](ROADMAP.md) for what's resolved and what's planned next (string literals, native OS surfaces, diagnostic quality improvements, and formal verification work). Self-hosting — Cinnabar compiling itself — is a long-term goal and completeness test, not a gate for any individual feature.

## Contributing

See [`CONTRIBUTING.md`](CONTRIBUTING.md) for how to set up a dev environment, the conventions this repository holds itself to, and how to run the verification gate. Report security-relevant bugs (soundness holes, memory-safety issues) per [`SECURITY.md`](SECURITY.md) rather than in a public issue.

## License

Apache-2.0 WITH LLVM-exception. See [`LICENSE`](LICENSE).
