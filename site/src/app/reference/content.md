<!--
  The three CLI sections below are named by src/content/cli.ts, which holds
  their order and nothing else. Each one reads four blocks: `<id>-heading`,
  `<id>-note`, an optional `<id>-intro`, and `<id>-rows`. Every `###` section
  of a `-rows` block is one table row — the heading is the flag or command,
  the paragraph under it is what it does.
-->

<!-- @lede -->

Given a source file, `cinnabar` runs the whole pipeline and writes a static
binary. Given a subcommand, it acts on the project whose `build.cnb` manifest is
discovered by walking upward from the supplied path.

<!-- @single-file-heading -->

Compiling a single file

<!-- @single-file-note -->

cinnabar <FILE> [FLAGS]

<!-- @single-file-intro -->

On success the compiler prints `Successfully compiled <input> to '<output>'.`
and exits 0. Any lex, parse, resolve, typecheck, borrow-check or codegen failure
is rendered as source-located diagnostics and exits non-zero. There is no
partial output: a build either produces its artifact or produces diagnostics.

<!-- @single-file-rows -->

### <FILE>

Input Cinnabar source file (positional, required), conventionally .cnb

### -o, --output <PATH>

Output binary path (defaults to the input path with .cnb stripped)

### --dump-ast

Parse only, pretty-print the AST, and exit — no resolve, typecheck,
borrow-check or codegen

### --dump-typed-ast

Run the full front end, then print the node arena with every attached fact —
resolved symbols, canonical type keys, linearity flags, variant tags, field
facts — and exit

### --print-layout

Run the full front end, then print ABI size, alignment, field offsets and enum
variant tags for every concrete struct, enum and native handle, and exit

### --emit-llvm

Write the emitter's LLVM IR (before optimization) to the input path with .ll and
stop

### --emit-obj

Optimize and assemble to a relocatable object at the input path with .o,
skipping the static link

### --explain-borrow[=human|json]

Attach secondary labels to borrow and linearity errors: which paths consume a
value, where it was bound and its linear type, where it was previously moved.
=json emits them as structured diagnostics instead

### --emit-json

Write the invocation's result to standard output as exactly one JSON document
instead of terminal text: cinnabar.ast.v1 under --dump-ast, cinnabar.typed-ast.v1
under --dump-typed-ast, cinnabar.layout.v1 under --print-layout, and otherwise
cinnabar.diagnostics.v1, which is empty when the program was accepted. A fact
with no Cinnabar source origin reports a null source rather than a fabricated
location. Cannot be combined with --run, which gives the program's own output the
same stream

### --run

Execute the produced binary after a successful build. cinnabar then exits 0 if
the program exited 0, and non-zero otherwise

### -O, --opt-level <LEVEL>

LLVM optimization level: 0, 1, 2, 3, s, z (default 2)

<!-- @project-heading -->

Working on a project

<!-- @project-note -->

cinnabar <COMMAND> [PATH]

<!-- @project-intro -->

PATH defaults to `.` and may be a project directory, a build.cnb, or a source
path inside the project — the manifest is found by walking upward from it either
way. `--target` currently accepts only `host`; run `cinnabar targets` for the
list and the state of each.

<!-- @project-rows -->

### cinnabar init [PATH]

Scaffold build.cnb, main.cnb and tests/smoke.cnb. Refuses to overwrite: if any
of the three exists, it writes none of them

### cinnabar build [PATH] [--target host]

Compile the manifest's ENTRY to <project>/target/<NAME>

### cinnabar run [PATH] [--target host]

Build, then execute the artifact. Exits 0 if the program exited 0, non-zero
otherwise

### cinnabar check [PATH]

Load, resolve, typecheck and borrow-check; stop before code generation. Needs no
LLVM and links nothing

### cinnabar test [PATH] [--update-snapshots]

Compile and run every .cnb file under the manifest's TESTS directory,
recursively

### cinnabar fmt [--check] <FILE>

Rewrite one file into canonical form, or with --check exit non-zero if it is not
already canonical

### cinnabar doc [PATH] [-o DIR]

Render every public declaration into <project>/target/doc/index.html

### cinnabar burn [PATH] [--address ADDR]

Serve those docs plus the manifesto over HTTP, pinned to this compiler's version
(default 127.0.0.1:7878)

<!-- @inspect-heading -->

Inspecting and experimenting

<!-- @inspect-note -->

Read-only and local-only surfaces

<!-- @inspect-rows -->

### cinnabar targets

List code-generation targets and whether this binary can build for each

### cinnabar inspect [PATH] [-o FILE]

Build, then report computed layouts alongside the linked binary's sections,
symbols and disassembly

### cinnabar soundness [PATH] [-o FILE]

Emit what the front end established, as JSON. Evidence, not a proof — the report
says formal_proof: false and scopes itself

### cinnabar playground [--address ADDR]

Serve a local page that compiles and runs submitted source. Loopback-only,
size-capped and time-limited by design (default 127.0.0.1:7879)

### cinnabar mushlings {init|verify} [PATH]

Exercises that teach the language through its own diagnostics; the real compiler
decides whether a fix is right

### cinnabar fuzz replay <FILE>

Recompile a saved fuzz artifact and report whether it still reproduces its
failure

### cinnabar fuzz minimize <FILE> [-o FILE]

Shrink an artifact to the smallest source with the same failure signature

### cinnabar native-stub <IDL> -o <FILE>

Generate a typed, opaque nat type / nat fun surface from the constrained native
IDL

<!-- @manifest -->

`build.cnb` is Cinnabar source, not a configuration format. It is read back
through the compiler's own front end, so it obeys the same casing, typing and
literal rules as any other program.

`NAME` names the built artifact and must be a single path component. `ENTRY` and
`TESTS` are relative paths confined to the project root. `TESTS` may be omitted,
and then defaults to `tests`.

`build` and `run` name the artifact after the manifest's `NAME` rather than after
whichever file happens to be the entry — a project that renames its entry source
has not renamed itself.

<!-- @test-layout-rows -->

### case.cnb

Must compile, link, and exit 0

### case.cnb.exit

The non-zero status case.cnb is expected to exit with

### case.reject.cnb

Must be rejected; compiling it successfully is a failure

### case.reject.cnb.stderr

The exact diagnostic that rejection must produce

<!-- @test-layout -->

A `.stderr` sidecar makes its test a rejection test whether or not the name says
`.reject`, and the snapshot is compared in full rather than searched for a
substring — a diagnostic is part of what the compiler promises, so a change to
its wording is a change to be reviewed. `--update-snapshots` is for deliberately
accepting a diagnostic whose diff you have read, not for making a red run go
green.

<!-- @profiles -->

Individual budgets can be overridden when a reduced profile is still broader or
narrower than needed. The full profile ignores these variables, so an exported
local override cannot silently reduce the gate's coverage.

<!-- @test-env-rows -->

### CINNABAR_FUZZ_POSITIVE_CASES

Generated valid programs compiled

### CINNABAR_FUZZ_NEGATIVE_CASES

Generated invalid linearity programs rejected

### CINNABAR_FUZZ_RUN_CASES

Valid fuzz programs additionally linked and executed

### CINNABAR_REPRO_RUN_CASES

Expected-success fixtures additionally linked and executed

### CINNABAR_REPRO_RECORD_CASES

Record-only fixtures compiled and run

### CINNABAR_REPRO_LINK_COMPILE_ONLY

Whether blocking compile-only fixtures are linked (true) instead of stopping at
LLVM IR (false)

### CINNABAR_TEST_RUN_TIMEOUT_SECS

Per-program execution timeout

### CINNABAR_TEST_COMPILE_TIMEOUT_SECS

Per-program fuzz compilation timeout

<!-- @self-documenting -->

Each command is documented in the binary itself — `cinnabar <COMMAND> --help`
prints the full description, not a one-line summary.
