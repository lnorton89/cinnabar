//! The CLI driver, and the `--dump-ast` arena pretty-printer.
//!
//! Wires the fixed pipeline together verbatim — load, resolve, typecheck,
//! borrow-check, codegen — and owns everything about how a diagnostic
//! reaches a terminal. Every stage's `Diag` tuples are rendered through
//! ariadne's `Report`/`Label`/`Source` with an `FnCache` that looks up
//! source text across the whole loaded module set, so a cross-file error
//! points into the right file. `--dump-ast` short-circuits after parsing
//! and prints the flat arena instead of continuing.
//!
//! The clap surface here is also the whole tool surface: the project
//! commands, the documentation and playground servers, the Mushlings
//! exercises, fuzz replay and minimization, the formatter, and the
//! inspection flags all dispatch from this file into the library.
//!
//! `--emit-json` selects the machine-readable rendering of whatever the
//! invocation produced, which `emit_json` and the files that own those
//! facts define. This file decides only which rendering a run gets, so a
//! consumer parses exactly one document per run — a diagnostic envelope
//! with an empty list where a terminal would have been told the program
//! compiled.
//!
//! **Invariants:**
//! - This is the only place a typed error may become a string. Every stage
//!   below carries its error, with a real span, until it arrives here —
//!   including on the way into the structured envelope.
//! - `NO_FILE` renders as a genuinely source-less error rather than as a
//!   location. A fact about a compiler-synthesized wrapper has no line in
//!   the user's program to point at, and inventing one would be a lie the
//!   user cannot act on.
//! - The pipeline order is fixed and a reporting stage halts it, so no
//!   stage ever runs on facts an earlier one failed to establish.

use cinnabar::ast::*;
use cinnabar::{advanced_tools, analysis, borrow, codegen, docs, module_loader, native_stub, project, resolver, typecheck};
use ariadne::{Color, FnCache, Label, Report, ReportKind, Source};
use clap::builder::PathBufValueParser;
use clap::{Arg, ArgAction, Command as ClapCommand};
use cinnabar::codegen::error::codegen_error_message;
use cinnabar::codegen::{compile_and_link, compile_to_ir, compile_to_object};
use serde_json::Value;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

struct CliArgs {
    input: PathBuf,
    output: Option<PathBuf>,
    dump_ast: bool,
    dump_typed_ast: bool,
    print_layout: bool,
    explain_borrow: Option<String>,
    emit_json: bool,
    run: bool,
    opt_level: String,
    emit_llvm: bool,
    emit_obj: bool,
    format_check: Option<bool>,
    check_only: bool,
    instrumented: bool,
    static_link: bool,
    target: String,
    tool_command: Option<ToolCommand>,
}

enum ToolCommand {
    // The output directory, and whether the caller wants the document
    // rather than the page.
    Doc(Option<PathBuf>, bool),
    Burn(String),
    Build(String),
    Run(String),
    Check,
    Test(bool),
    Init,
    NativeStub,
    Inspect,
    Targets,
    MushlingsInit,
    MushlingsVerify,
    FuzzReplay,
    FuzzMinimize,
    Soundness,
    Playground(String),
    Snapshots(String, bool),
}

fn project_path_arg() -> Arg {
    Arg::new("project_path")
        .value_name("PATH")
        .default_value(".")
        .value_parser(PathBufValueParser::new())
        .help("Project directory, build.cnb, or source path within the project")
}

fn parse_args() -> Option<CliArgs> {
    let matches = ClapCommand::new("cinnabar")
        .about("Cinnabar compiler")
        .long_about(
            "Cinnabar compiler.\n\n\
             There are two ways to invoke it. Given a source FILE, it runs the whole \
             pipeline — lex, parse, load modules, resolve, typecheck, borrow-check, \
             generate code, link — and writes a dynamically linked binary by default. Given a subcommand, it \
             acts on the project whose 'build.cnb' manifest is discovered by walking \
             upward from the supplied path.\n\n\
             Diagnostics are errors only. There is no warning severity, no suppression \
             pragma, and no flag that turns a check off: a program either compiles \
             cleanly or is rejected with a source-located diagnostic.",
        )
        .after_help(
            "Examples:\n  \
             cinnabar main.cnb -o main        Compile one file to a native binary\n  \
             cinnabar main.cnb --run          Compile it and execute the result\n  \
             cinnabar build                   Build the project containing the current directory\n  \
             cinnabar test                    Run the project's test suite\n\n\
             Run 'cinnabar <COMMAND> --help' for the full description of a command.",
        )
        .subcommand_negates_reqs(true)
        .arg(
            Arg::new("input")
                .value_name("FILE")
                .required(true)
                .value_parser(PathBufValueParser::new())
                .help("Input Cinnabar source file"),
        )
        .arg(
            Arg::new("output")
                .short('o')
                .long("output")
                .value_name("PATH")
                .value_parser(PathBufValueParser::new())
                .help("Output binary path"),
        )
        .arg(
            Arg::new("dump_ast")
                .long("dump-ast")
                .action(ArgAction::SetTrue)
                .help("Print the parsed AST and exit"),
        )
        .arg(
            Arg::new("dump_typed_ast")
                .long("dump-typed-ast")
                .action(ArgAction::SetTrue)
                .conflicts_with_all(["dump_ast", "emit_llvm", "emit_obj", "run"])
                .help("Run the full front-end (resolve, typecheck, borrow-check), then print the node arena with every attached fact and exit"),
        )
        .arg(
            Arg::new("explain_borrow")
                .long("explain-borrow")
                .num_args(0..=1)
                .require_equals(true)
                .default_missing_value("human")
                .value_parser(clap::builder::PossibleValuesParser::new(["human", "json"]))
                .help("Explain borrow/linearity errors with secondary labels, or emit structured diagnostics with --explain-borrow=json"),
        )
        .arg(
            Arg::new("emit_json")
                .long("emit-json")
                .action(ArgAction::SetTrue)
                .conflicts_with("run")
                .help("Write this invocation's result to standard output as one JSON document: the arena under --dump-ast/--dump-typed-ast, the layout report under --print-layout, and otherwise the diagnostics, empty when the program is accepted"),
        )
        .arg(
            Arg::new("print_layout")
                .long("print-layout")
                .action(ArgAction::SetTrue)
                .conflicts_with_all(["dump_ast", "dump_typed_ast", "emit_llvm", "emit_obj", "run"])
                .help("Run the full front-end, then print size/alignment/field offsets for every concrete struct, enum, and native handle and exit"),
        )
        .arg(
            Arg::new("run")
                .long("run")
                .action(ArgAction::SetTrue)
                .conflicts_with_all(["emit_llvm", "emit_obj"])
                .help("Execute the compiled binary after building"),
        )
        .arg(
            Arg::new("opt_level")
                .short('O')
                .long("opt-level")
                .value_name("LEVEL")
                .value_parser(clap::builder::PossibleValuesParser::new(["0", "1", "2", "3", "s", "z"]))
                .help("Optimization level: 0, 1, 2, 3, s, z (default 2)"),
        )
        .arg(
            Arg::new("emit_llvm")
                .long("emit-llvm")
                .action(ArgAction::SetTrue)
                .conflicts_with("emit_obj")
                .help("Write the emitted LLVM IR (before optimization) and stop; default output is the input path with .ll"),
        )
        .arg(
            Arg::new("emit_obj")
                .long("emit-obj")
                .action(ArgAction::SetTrue)
                .help("Optimize and assemble to a relocatable object file, skipping the link; default output is the input path with .o"),
        )
        .arg(
            Arg::new("instrumented")
                .long("instrumented")
                .hide(true)
                .action(ArgAction::SetTrue)
                .conflicts_with_all(["dump_ast", "dump_typed_ast", "print_layout", "emit_llvm", "emit_obj", "check_only"])
                .help("Link dynamically against the host libc so a memory checker can interpose; test infrastructure, never a release artifact"),
        )
        .arg(
            Arg::new("static")
                .long("static")
                .action(ArgAction::SetTrue)
                .conflicts_with_all(["instrumented", "emit_llvm", "emit_obj", "check_only"])
                .help("Link with the embedded musl runtime (Linux builds with the static-musl feature only)"),
        )
        .arg(target_arg())
        .arg(
            Arg::new("check_only")
                .long("check-only")
                .hide(true)
                .action(ArgAction::SetTrue)
                .conflicts_with_all(["dump_ast", "dump_typed_ast", "print_layout", "emit_llvm", "emit_obj", "run"])
                .help("Stop after the front end without generating code; how 'cinnabar check' drives this binary"),
        )
        .subcommand(
            ClapCommand::new("fmt")
                .about("Format Cinnabar source in place")
                .long_about(
                    "Rewrite FILE into canonical Cinnabar formatting.\n\n\
                     The formatter takes no style options. Canonical form is one fixed \
                     shape, so there is nothing to configure and nothing left to argue \
                     about in review. The file is rewritten in place, and a file that is \
                     already canonical is left untouched and reported as such.\n\n\
                     With --check nothing is written. An already-canonical file exits 0; \
                     any other file is named on stderr and exits nonzero, which is the \
                     shape a CI job or a pre-commit hook wants.",
                )
                .arg(
                    Arg::new("fmt_input")
                        .value_name("FILE")
                        .required(true)
                        .value_parser(PathBufValueParser::new())
                        .help("Cinnabar source file to format"),
                )
                .arg(
                    Arg::new("check")
                        .long("check")
                        .action(ArgAction::SetTrue)
                        .help("Exit unsuccessfully if the file is not canonically formatted"),
                ),
        )
        .subcommand(
            ClapCommand::new("doc")
                .about("Generate HTML documentation for public Cinnabar declarations")
                .long_about(
                    "Render every public declaration reachable from the entry source into \
                     a single HTML page.\n\n\
                     The prose comes from the doc comments the parser attached to each \
                     item, and visibility is the 'pub' the resolver already established. \
                     This command does not re-scan source for comment syntax and does not \
                     re-decide what is public, so what appears is exactly what the \
                     compiler saw. A declaration that is not 'pub' is absent, and so is \
                     its documentation.\n\n\
                     PATH may be a project directory, a 'build.cnb', or a '.cnb' source \
                     file to document on its own. The page is written to \
                     <project>/target/doc/index.html unless -o names another directory.",
                )
                .arg(project_path_arg())
                .arg(
                    Arg::new("doc_output")
                        .short('o')
                        .long("output")
                        .value_name("DIR")
                        .value_parser(PathBufValueParser::new())
                        .help("Documentation output directory (default: target/doc)"),
                )
                .arg(
                    Arg::new("doc_emit_json")
                        .long("emit-json")
                        .action(ArgAction::SetTrue)
                        .help("Write the public API as one JSON document on standard output instead of rendering a page"),
                ),
        )
        .subcommand(
            ClapCommand::new("burn")
                .about("Serve version-pinned Cinnabook documentation locally")
                .long_about(
                    "Serve the Cinnabook — this project's API documentation folded \
                     together with the language manifesto — over HTTP.\n\n\
                     The page is pinned to the version of the compiler serving it, so \
                     what it says about the language is what this binary actually \
                     implements rather than what the latest published documentation \
                     says. That is the whole reason the manifesto is served from the \
                     compiler instead of linked from it.\n\n\
                     Nothing is written to disk; the page is rendered per request. The \
                     server runs until interrupted.",
                )
                .arg(project_path_arg())
                .arg(
                    Arg::new("address")
                        .long("address")
                        .default_value("127.0.0.1:7878")
                        .help("Local address to bind"),
                ),
        )
        .subcommand(
            ClapCommand::new("build")
                .about("Build the current Cinnabar project")
                .long_about(
                    "Compile the project's entry source into a static binary.\n\n\
                     The manifest is found by walking upward from PATH to the nearest \
                     'build.cnb', so any path inside a project works and the default of \
                     '.' builds the project you are standing in.\n\n\
                     The artifact is named by the manifest's NAME field, not by whichever \
                     file happens to be ENTRY — a project that renames its entry source \
                     has not renamed itself — and is written to <project>/target/<NAME>.\n\n\
                     A build is all or nothing. A failure in any stage is reported as a \
                     source-located diagnostic and no artifact is written.",
                )
                .arg(project_path_arg())
                .arg(target_arg()),
        )
        .subcommand(
            ClapCommand::new("run")
                .about("Build and run the current Cinnabar project")
                .long_about(
                    "Build the project exactly as 'cinnabar build' does, then execute the \
                     resulting binary.\n\n\
                     The program inherits this terminal, so its output and input are its \
                     own. Its exit status is reported rather than forwarded: 'run' exits 0 \
                     when the program exited 0 and nonzero otherwise, so a program whose \
                     specific status code matters should be executed directly from \
                     <project>/target/<NAME>.",
                )
                .arg(project_path_arg())
                .arg(target_arg()),
        )
        .subcommand(
            ClapCommand::new("check")
                .about("Run the compiler front-end without code generation")
                .long_about(
                    "Run the front end over the project — load, resolve, typecheck, \
                     borrow-check — and stop before code generation.\n\n\
                     Everything that decides whether a program is legal Cinnabar has \
                     happened by then: name resolution, casing, types, match \
                     exhaustiveness, and the borrow and linearity rules. So this is the \
                     fast answer to 'is this program valid', and it neither optimizes nor \
                     links.\n\n\
                     It is not a laxer build. The stages it runs are the same stages \
                     'build' runs and reach the same verdicts; it simply stops once the \
                     front end has established everything it can establish without \
                     emitting code.",
                )
                .arg(project_path_arg()),
        )
        .subcommand(
            ClapCommand::new("test")
                .about("Discover and run project tests")
                .long_about(
                    "Compile and run every '.cnb' file under the manifest's TESTS \
                     directory, recursively.\n\n\
                     A test file's name states what is expected of it:\n\n  \
                     case.cnb                must compile, link, and exit 0\n  \
                     case.cnb.exit           the nonzero status 'case.cnb' must exit with\n  \
                     case.reject.cnb         must be rejected; compiling it is a failure\n  \
                     case.reject.cnb.stderr  the exact diagnostic that rejection must produce\n\n\
                     A '.stderr' sidecar makes its test a rejection test whether or not the \
                     name says '.reject', and the snapshot is compared in full rather than \
                     searched for a substring: a diagnostic is part of what the compiler \
                     promises, so a change to its wording is a change to be reviewed.\n\n\
                     --update-snapshots rewrites those sidecars from what the compiler \
                     currently prints. It is for deliberately accepting a diagnostic you \
                     have read the diff of, never for making a red run go green.",
                )
                .arg(project_path_arg())
                .arg(
                    Arg::new("update_snapshots")
                        .long("update-snapshots")
                        .action(ArgAction::SetTrue)
                        .help("Replace diagnostic .stderr snapshots for rejection tests"),
                ),
        )
        .subcommand(
            ClapCommand::new("init")
                .about("Scaffold a Cinnabar project")
                .long_about(
                    "Write a new project into PATH: a 'build.cnb' manifest, a 'main.cnb' \
                     that returns 0, and 'tests/smoke.cnb'.\n\n\
                     The manifest is Cinnabar source, not a configuration format. It is \
                     read back through the compiler's own front end, so it obeys the same \
                     casing, typing, and literal rules as any other program:\n\n  \
                     pub const NAME: &[U8] = \"<directory name>\"\n  \
                     pub const ENTRY: &[U8] = \"main.cnb\"\n  \
                     pub const TESTS: &[U8] = \"tests\"\n\n\
                     NAME names the built artifact and must be a single path component. \
                     ENTRY and TESTS are relative paths confined to the project root. \
                     TESTS may be omitted and then defaults to 'tests'.\n\n\
                     Nothing is ever overwritten: if any of the three files already \
                     exists, init refuses and writes none of them.",
                )
                .arg(project_path_arg()),
        )
        .subcommand(
            ClapCommand::new("native-stub")
                .about("Generate a typed Cinnabar native surface from the constrained native IDL")
                .long_about(
                    "Translate a native IDL description into the 'nat type' and 'nat fun' \
                     declarations that expose it to Cinnabar code.\n\n\
                     The generated surface is opaque by construction: a native type \
                     becomes a handle, never a pointer user code can see through. \
                     Generating it is what keeps the declarations and the runtime from \
                     drifting apart, so the output is meant to be regenerated rather than \
                     hand-edited.",
                )
                .arg(
                    Arg::new("project_path")
                        .value_name("IDL")
                        .required(true)
                        .value_parser(PathBufValueParser::new())
                        .help("Native IDL description to translate"),
                )
                .arg(
                    Arg::new("output")
                        .short('o')
                        .long("output")
                        .value_name("FILE")
                        .required(true)
                        .value_parser(PathBufValueParser::new())
                        .help("Cinnabar source file to write the generated surface to"),
                ),
        )
        .subcommand(
            ClapCommand::new("inspect")
                .about("Build and inspect layouts, sections, symbols, and disassembly")
                .long_about(
                    "Build the project, then report what was actually produced: the ABI \
                     size, alignment, and field offsets the compiler computed, alongside \
                     the linked binary's sections, symbols, and disassembly.\n\n\
                     This is the answer to 'what did my declarations become', and it reads \
                     the real artifact rather than predicting it. The report is printed \
                     unless -o names a file to write it to.",
                )
                .arg(project_path_arg())
                .arg(
                    Arg::new("output")
                        .short('o')
                        .long("output")
                        .value_name("FILE")
                        .value_parser(PathBufValueParser::new())
                        .help("Write the report to FILE instead of standard output"),
                ),
        )
        .subcommand(
            ClapCommand::new("targets")
                .about("List code-generation targets and their availability")
                .long_about(
                    "List each code-generation target and say plainly whether this binary \
                     can build for it.\n\n\
                     A target is listed as available only when it is; a planned target \
                     names what it is still waiting on. Nothing here silently degrades to \
                     the host.",
                ),
        )
        .subcommand(
            ClapCommand::new("mushlings").about("Interactive compiler-learning exercises")
                .long_about(
                    "Interactive exercises that teach the language through its own \
                     diagnostics.\n\n\
                     Each exercise is a program that does not compile. You fix it, and the \
                     real compiler decides whether you were right — there is no separate \
                     answer key that could disagree with the compiler. Exercises exist \
                     only where the language has a settled rule and a real diagnostic to \
                     teach it with.",
                )
                .subcommand_required(true)
                .subcommand(
                    ClapCommand::new("init")
                        .about("Write the exercise set into PATH")
                        .arg(project_path_arg()),
                )
                .subcommand(
                    ClapCommand::new("verify")
                        .about("Recompile the exercises in PATH and report which are solved")
                        .arg(project_path_arg()),
                ),
        )
        .subcommand(
            ClapCommand::new("fuzz").about("Replay and minimize saved fuzz artifacts")
                .long_about(
                    "Work with the source artifacts saved by a fuzzing run.\n\n\
                     'replay' answers whether an artifact still reproduces its failure. \
                     'minimize' shrinks one to the smallest source that reproduces the \
                     same failure — the same failure specifically, since a smaller program \
                     that fails for a new reason has stopped being evidence about the bug \
                     being minimized.",
                )
                .subcommand_required(true)
                .subcommand(
                    ClapCommand::new("replay")
                        .about("Recompile a saved artifact and report whether it still fails")
                        .arg(
                            Arg::new("project_path")
                                .value_name("FILE")
                                .required(true)
                                .value_parser(PathBufValueParser::new())
                                .help("Saved fuzz artifact to replay"),
                        ),
                )
                .subcommand(
                    ClapCommand::new("minimize")
                        .about("Shrink an artifact to the smallest source with the same failure")
                        .arg(
                            Arg::new("project_path")
                                .value_name("FILE")
                                .required(true)
                                .value_parser(PathBufValueParser::new())
                                .help("Saved fuzz artifact to minimize"),
                        )
                        .arg(
                            Arg::new("output")
                                .short('o')
                                .long("output")
                                .value_name("FILE")
                                .value_parser(PathBufValueParser::new())
                                .help("Where to write the minimized artifact (default: alongside the input)"),
                        ),
                ),
        )
        .subcommand(
            ClapCommand::new("soundness")
                .about("Emit machine-checkable front-end soundness evidence")
                .long_about(
                    "Emit, as JSON, what the front end actually established about a \
                     program: how much of it was resolved, typed, and borrow-checked, and \
                     how many diagnostics that produced.\n\n\
                     This is evidence, not a proof. The report states 'formal_proof: \
                     false' and scopes itself explicitly, because it counts checks the \
                     compiler ran — it is not a mechanized preservation and progress \
                     argument, and must not be read as one.\n\n\
                     Written to <project>/target/soundness-evidence.json unless -o says \
                     otherwise.",
                )
                .arg(project_path_arg())
                .arg(
                    Arg::new("output")
                        .short('o')
                        .long("output")
                        .value_name("FILE")
                        .value_parser(PathBufValueParser::new())
                        .help("Write the evidence to FILE instead of target/soundness-evidence.json"),
                ),
        )
        .subcommand(
            ClapCommand::new("snapshots")
                .about("Review diagnostic snapshot changes one fixture at a time")
                .long_about(
                    "Serve a local page showing every rejection test in the project \
                     beside the diagnostic its '.stderr' sidecar records and the one \
                     the compiler prints now.\n\n\
                     'cinnabar test --update-snapshots' accepts every changed snapshot \
                     at once, which is the wrong granularity for the change that most \
                     often produces them: improving a diagnostic rewrites many \
                     snapshots, most of them better and one of them by accident. Here \
                     each fixture is accepted or left alone on its own, and accepting \
                     writes that one sidecar.\n\n\
                     The comparison shown is the one 'cinnabar test' makes, not a \
                     second one. It binds a loopback address only: it writes files in \
                     your project on request.\n\n\
                     With --emit-json the same report is written to standard output \
                     instead of served, for a reviewer that is not a browser.",
                )
                .arg(project_path_arg())
                .arg(
                    Arg::new("address")
                        .long("address")
                        .default_value("127.0.0.1:7880")
                        .help("Loopback address to bind"),
                )
                .arg(
                    Arg::new("snapshots_emit_json")
                        .long("emit-json")
                        .action(ArgAction::SetTrue)
                        .help("Write the report to standard output as one JSON document instead of serving it"),
                ),
        )
        .subcommand(
            ClapCommand::new("playground")
                .about("Serve a loopback-only local Cinnabar playground")
                .long_about(
                    "Serve a local page that compiles and runs submitted Cinnabar source.\n\n\
                     It compiles and executes arbitrary code, so it is deliberately a \
                     local tool: it binds a loopback address only, caps the size of a \
                     submission, and runs each program under a wall-clock limit. Do not \
                     put it behind a public address.",
                )
                .arg(
                    Arg::new("address")
                        .long("address")
                        .default_value("127.0.0.1:7879")
                        .help("Loopback address to bind"),
                ),
        )
        .get_matches();
    if let Some(format_matches) = matches.subcommand_matches("fmt") {
        let input = {
            let path = format_matches.get_one::<PathBuf>("fmt_input")?;
            path.clone()
        };
        return Some(CliArgs {
            input,
            output: None,
            dump_ast: false,
            dump_typed_ast: false,
            print_layout: false,
            explain_borrow: None,
            emit_json: false,
            run: false,
            opt_level: "2".to_string(),
            emit_llvm: false,
            emit_obj: false,
            format_check: Some(format_matches.get_flag("check")),
            check_only: false,
            instrumented: false,
            static_link: false,
            target: "host".to_string(),
            tool_command: None,
        });
    }
    let subcommands = ["doc", "burn", "build", "run", "check", "test", "init", "native-stub", "inspect", "soundness"];
    for subcommand_name in subcommands {
        if let Some(subcommand_matches) = matches.subcommand_matches(subcommand_name) {
            let input = subcommand_matches.get_one::<PathBuf>("project_path")?.clone();
            let tool_command = if subcommand_name == "doc" {
                ToolCommand::Doc(
                    subcommand_matches.get_one::<PathBuf>("doc_output").cloned(),
                    subcommand_matches.get_flag("doc_emit_json"),
                )
            } else if subcommand_name == "burn" {
                let address = subcommand_matches.get_one::<String>("address")?.clone();
                ToolCommand::Burn(address)
            } else if subcommand_name == "build" {
                ToolCommand::Build(subcommand_matches.get_one::<String>("target")?.clone())
            } else if subcommand_name == "run" {
                ToolCommand::Run(subcommand_matches.get_one::<String>("target")?.clone())
            } else if subcommand_name == "check" {
                ToolCommand::Check
            } else if subcommand_name == "test" {
                ToolCommand::Test(subcommand_matches.get_flag("update_snapshots"))
            } else if subcommand_name == "init" {
                ToolCommand::Init
            } else if subcommand_name == "native-stub" {
                ToolCommand::NativeStub
            } else if subcommand_name == "inspect" {
                ToolCommand::Inspect
            } else {
                ToolCommand::Soundness
            };
            let tool_output = if subcommand_name == "native-stub" || subcommand_name == "inspect" || subcommand_name == "soundness" {
                subcommand_matches.get_one::<PathBuf>("output").cloned()
            } else {
                None
            };
            return Some(CliArgs {
                input,
                output: tool_output,
                dump_ast: false,
                dump_typed_ast: false,
                print_layout: false,
                explain_borrow: None,
                emit_json: false,
                run: false,
                opt_level: "2".to_string(),
                emit_llvm: false,
                emit_obj: false,
                format_check: None,
                check_only: false,
                instrumented: false,
                static_link: false,
                target: "host".to_string(),
                tool_command: Some(tool_command),
            });
        }
    }
    if matches.subcommand_matches("targets").is_some() {
        return Some(tool_args(PathBuf::from("."), ToolCommand::Targets, None));
    }
    if let Some(mushlings) = matches.subcommand_matches("mushlings") {
        if let Some(init) = mushlings.subcommand_matches("init") {
            return Some(tool_args(init.get_one::<PathBuf>("project_path")?.clone(), ToolCommand::MushlingsInit, None));
        }
        if let Some(verify) = mushlings.subcommand_matches("verify") {
            return Some(tool_args(verify.get_one::<PathBuf>("project_path")?.clone(), ToolCommand::MushlingsVerify, None));
        }
    }
    if let Some(fuzz) = matches.subcommand_matches("fuzz") {
        if let Some(replay) = fuzz.subcommand_matches("replay") {
            return Some(tool_args(replay.get_one::<PathBuf>("project_path")?.clone(), ToolCommand::FuzzReplay, None));
        }
        if let Some(minimize) = fuzz.subcommand_matches("minimize") {
            return Some(tool_args(minimize.get_one::<PathBuf>("project_path")?.clone(), ToolCommand::FuzzMinimize, minimize.get_one::<PathBuf>("output").cloned()));
        }
    }
    if let Some(snapshots) = matches.subcommand_matches("snapshots") {
        return Some(tool_args(
            snapshots.get_one::<PathBuf>("project_path")?.clone(),
            ToolCommand::Snapshots(
                snapshots.get_one::<String>("address")?.clone(),
                snapshots.get_flag("snapshots_emit_json"),
            ),
            None,
        ));
    }
    if let Some(playground) = matches.subcommand_matches("playground") {
        return Some(tool_args(PathBuf::from("."), ToolCommand::Playground(playground.get_one::<String>("address")?.clone()), None));
    }
    let input = {
        let path = matches.get_one::<PathBuf>("input")?;
        path.clone()
    };
    let output = matches.get_one::<PathBuf>("output").cloned();
    let opt_level = matches
        .get_one::<String>("opt_level")
        .cloned()
        .unwrap_or_else(|| "2".to_string());
    Some(CliArgs {
        input,
        output,
        dump_ast: matches.get_flag("dump_ast"),
        dump_typed_ast: matches.get_flag("dump_typed_ast"),
        print_layout: matches.get_flag("print_layout"),
        explain_borrow: matches.get_one::<String>("explain_borrow").cloned(),
        emit_json: matches.get_flag("emit_json"),
        run: matches.get_flag("run"),
        opt_level,
        emit_llvm: matches.get_flag("emit_llvm"),
        emit_obj: matches.get_flag("emit_obj"),
        format_check: None,
        check_only: matches.get_flag("check_only"),
        instrumented: matches.get_flag("instrumented"),
        static_link: matches.get_flag("static"),
        target: matches.get_one::<String>("target").cloned().unwrap_or_else(|| "host".to_string()),
        tool_command: None,
    })
}

fn target_arg() -> Arg {
    Arg::new("target").long("target").default_value("host").help("Compilation target: host, linux, darwin, bsd, or windows")
}

fn tool_args(input: PathBuf, tool_command: ToolCommand, output: Option<PathBuf>) -> CliArgs {
    CliArgs { input, output, dump_ast: false, dump_typed_ast: false, print_layout: false, explain_borrow: None, emit_json: false, run: false, opt_level: "2".to_string(), emit_llvm: false, emit_obj: false, format_check: None, check_only: false, instrumented: false, static_link: false, target: "host".to_string(), tool_command: Some(tool_command) }
}

fn main() -> ExitCode {
    let args = match parse_args() {
        Some(args) => args,
        None => return ExitCode::FAILURE,
    };
    if let Some(check) = args.format_check {
        return format_file(&args.input, check);
    }
    if let Some(tool_command) = args.tool_command {
        return run_tool_command(&args.input, args.output.as_deref(), tool_command);
    }
    let mut names: Vec<String> = Vec::new();
    let mut nodes: Vec<i64> = Vec::new();
    let mut lists: Vec<Vec<i64>> = Vec::new();
    let mut errors: Vec<Diag> = Vec::new();
    let mut notes: Vec<Note> = Vec::new();
    let mut deferred: Vec<Diag> = Vec::new();
    let entry = args.input.to_string_lossy().to_string();
    let json_out = args.emit_json;
    let (loaded, files) = module_loader::load(&mut names, &mut nodes, &mut lists, &mut errors, &entry);
    let (root, ext_mods) = match loaded {
        Some(program) => program,
        None => return report_diagnostics(json_out, &errors, &[], &files),
    };
    if args.dump_ast {
        if json_out {
            return emit_report(&cinnabar::inspect::arena_json(
                &names,
                &nodes,
                &lists,
                root,
                &files,
                cinnabar::emit_json::AST_FORMAT,
            ));
        }
        dump_program(&names, &nodes, &lists, root);
        return ExitCode::SUCCESS;
    }
    let resolver_diagnostics = resolver::Diagnostics {
        errors: &mut errors,
        notes: &mut notes,
        deferred: &mut deferred,
    };
    if !resolver::resolve(&mut names, &mut nodes, &mut lists, resolver_diagnostics, root, &ext_mods) {
        return report_diagnostics(json_out, &errors, &notes, &files);
    }
    let (ok, impls_list) = typecheck::typecheck(&mut names, &mut nodes, &mut lists, &mut errors, &mut notes, root, &ext_mods);
    if !ok {
        return report_diagnostics(json_out, &errors, &notes, &files);
    }
    if !borrow::borrow_check(&mut names, &mut nodes, &mut lists, &mut errors, &mut notes, root, &ext_mods) {
        // The structured envelope always carries the checker's notes: a
        // consumer asked for machine-readable output, and there is no
        // terminal to keep uncluttered. --explain-borrow=json is the older
        // spelling of that same request.
        if json_out || args.explain_borrow.as_deref() == Some("json") {
            return report_diagnostics(true, &errors, &notes, &files);
        }
        let shown_notes: &[Note] = if args.explain_borrow.as_deref() == Some("human") {
            &notes
        } else {
            &[]
        };
        return finish_with_diagnostics(&errors, shown_notes, &files);
    }
    // Unused items are reported here rather than from the resolver. A file
    // with a type or borrow error is told about that error; reporting
    // reachability first would stop the pipeline and answer a broken program
    // with a list of things nothing calls.
    if !deferred.is_empty() {
        return report_diagnostics(json_out, &deferred, &[], &files);
    }
    if args.dump_typed_ast {
        if json_out {
            return emit_report(&cinnabar::inspect::arena_json(
                &names,
                &nodes,
                &lists,
                root,
                &files,
                cinnabar::emit_json::TYPED_AST_FORMAT,
            ));
        }
        print!("{}", cinnabar::inspect::dump_typed_arena(&names, &nodes, &lists));
        return ExitCode::SUCCESS;
    }
    if args.check_only {
        return report_accepted(json_out, &format!("{} passed all front-end checks.", entry));
    }
    if args.print_layout {
        if json_out {
            return match cinnabar::codegen::layout::layouts_json(&names, &mut nodes, &mut lists) {
                Ok(report) => emit_report(&report),
                Err(codegen_err) => report_codegen_error(json_out, &codegen_err, &files),
            };
        }
        match cinnabar::codegen::layout::render_layouts(&names, &mut nodes, &mut lists) {
            Ok(report) => {
                print!("{}", report);
                return ExitCode::SUCCESS;
            }
            Err(codegen_err) => return finish_with_codegen_error(&codegen_err, &files),
        }
    }
    let entry_span = entry_span_of(&files);
    if args.emit_llvm {
        let out = emit_out_path(&args, "ll");
        let written = compile_to_ir(&names, &mut nodes, &mut lists, impls_list, entry_span, &args.target)
            .and_then(|ir_text| write_output_text(&out, &ir_text));
        if let Err(codegen_err) = written {
            return report_codegen_error(json_out, &codegen_err, &files);
        }
        return report_accepted(json_out, &format!("Emitted LLVM IR for {} to '{}'.", entry, out.display()));
    }
    if args.emit_obj {
        let out = emit_out_path(&args, "o");
        // Object emission stops before linking, so the link mode is never
        // consulted; it is carried only to share BuildTarget with the link
        // path.
        let target = codegen::BuildTarget {
            out: &out,
            opt_level: &args.opt_level,
            mode: codegen::LinkMode::Dynamic,
            platform: &args.target,
        };
        if let Err(codegen_err) =
            compile_to_object(&names, &mut nodes, &mut lists, impls_list, &target, entry_span)
        {
            return report_codegen_error(json_out, &codegen_err, &files);
        }
        return report_accepted(json_out, &format!("Emitted object file for {} to '{}'.", entry, out.display()));
    }
    let out = match &args.output {
        Some(path) => path.clone(),
        None => default_out_path(&args.input),
    };
    if args.static_link && (args.target != "host" && args.target != "linux" || !cfg!(all(feature = "static-musl", target_os = "linux"))) {
        // A refusal about how this binary was built has no line of the
        // user's program to point at, so it travels as a source-less
        // diagnostic — through the same reporter, and into the same
        // envelope, as every other one.
        let unsupported: Diag = (
            "--static requires a Linux compiler built with the static-musl feature".to_string(),
            NO_FILE,
            0,
            0,
        );
        return report_diagnostics(json_out, &[unsupported], &[], &files);
    }
    let target = codegen::BuildTarget {
        out: &out,
        opt_level: &args.opt_level,
        mode: if args.instrumented {
            codegen::LinkMode::Instrumented
        } else if args.static_link {
            codegen::LinkMode::StaticMusl
        } else if args.target == "windows" || (args.target == "host" && cfg!(target_os = "windows")) {
            codegen::LinkMode::WindowsMinGW
        } else {
            codegen::LinkMode::Dynamic
        },
        platform: &args.target,
    };
    if let Err(codegen_err) = compile_and_link(&names, &mut nodes, &mut lists, impls_list, &target, entry_span) {
        return report_codegen_error(json_out, &codegen_err, &files);
    }
    if args.run {
        return run_binary(&out);
    }
    report_accepted(json_out, &format!("Successfully compiled {} to '{}'.", entry, out.display()))
}

/// Report a run that produced no diagnostics.
///
/// A `--emit-json` invocation writes exactly one document whether or not
/// the program was accepted, so a clean run is an empty diagnostic list
/// rather than a status line a consumer would have to recognize as "not an
/// error". A terminal gets the sentence it has always been given.
fn report_accepted(emit_json: bool, message: &str) -> ExitCode {
    if emit_json {
        return emit_report(&cinnabar::emit_json::diagnostics_report(&[], &[], &[]));
    }
    println!("{}", message);
    ExitCode::SUCCESS
}

/// End the run with diagnostics, in whichever rendering was asked for.
fn report_diagnostics(emit_json: bool, errors: &[Diag], notes: &[Note], files: &[(String, String)]) -> ExitCode {
    if emit_json {
        return finish_with_diagnostics_json(errors, notes, files);
    }
    finish_with_diagnostics(errors, notes, files)
}

/// End the run with a codegen failure, in whichever rendering was asked
/// for. It enters the structured envelope as the diagnostic it is, so a
/// consumer needs no second shape for failures below the front end.
fn report_codegen_error(emit_json: bool, codegen_err: &codegen::error::CodegenError, files: &[(String, String)]) -> ExitCode {
    if emit_json {
        let diag: Diag = (
            codegen_error_message(codegen_err),
            codegen_err.span.0,
            codegen_err.span.1,
            codegen_err.span.2,
        );
        return finish_with_diagnostics_json(&[diag], &[], files);
    }
    finish_with_codegen_error(codegen_err, files)
}

/// Write one JSON document to standard output.
///
/// A serialization failure is still a compiler failure and is reported
/// through the same source-less reporter every other tool error uses,
/// rather than leaving the consumer with empty output and a success status.
fn emit_report(report: &Value) -> ExitCode {
    match cinnabar::emit_json::render_report(report) {
        Ok(rendered) => {
            println!("{}", rendered);
            ExitCode::SUCCESS
        }
        Err(message) => source_less_failure(&message),
    }
}

fn format_file(path: &Path, check: bool) -> ExitCode {
    let source = match std::fs::read_to_string(path) {
        Ok(text) => text,
        Err(read_err) => {
            let message = format!("cannot read source file '{}': {}", path.display(), read_err);
            if render_source_less(&message).is_err() {
                return ExitCode::FAILURE;
            }
            return ExitCode::FAILURE;
        }
    };
    let formatted = cinnabar::format::format_source(&source);
    if check {
        if formatted == source {
            return ExitCode::SUCCESS;
        }
        eprintln!("{} is not canonically formatted", path.display());
        return ExitCode::FAILURE;
    }
    if formatted == source {
        println!("{} is already formatted.", path.display());
        return ExitCode::SUCCESS;
    }
    match std::fs::write(path, formatted) {
        Ok(()) => {
            println!("Formatted {}.", path.display());
            ExitCode::SUCCESS
        }
        Err(write_err) => {
            let message = format!("cannot write source file '{}': {}", path.display(), write_err);
            if render_source_less(&message).is_err() {
                return ExitCode::FAILURE;
            }
            ExitCode::FAILURE
        }
    }
}

fn run_tool_command(path: &Path, output: Option<&Path>, command: ToolCommand) -> ExitCode {
    match command {
        ToolCommand::Doc(output, emit_json) => generate_documentation(path, output.as_deref(), false, None, emit_json),
        ToolCommand::Burn(address) => generate_documentation(path, None, true, Some(&address), false),
        ToolCommand::Build(target) => run_project_compiler(path, false, false, &target),
        ToolCommand::Run(target) => run_project_compiler(path, true, false, &target),
        ToolCommand::Check => run_project_compiler(path, false, true, "host"),
        ToolCommand::Test(update_snapshots) => run_project_tests(path, update_snapshots),
        ToolCommand::Init => initialize_project(path),
        ToolCommand::NativeStub => generate_native_stub(path, output),
        ToolCommand::Inspect => inspect_binary(path, output),
        ToolCommand::Targets => {
            println!("host\tavailable\t{}", advanced_tools::host_target());
            println!("linux\tavailable\tPOSIX C runtime");
            println!("darwin\tavailable\tPOSIX C runtime");
            println!("bsd\tavailable\tPOSIX C runtime");
            println!("windows\tavailable\tMinGW C runtime");
            ExitCode::SUCCESS
        }
        ToolCommand::MushlingsInit => initialize_mushlings(path),
        ToolCommand::MushlingsVerify => verify_mushlings(path),
        ToolCommand::FuzzReplay => replay_fuzz(path),
        ToolCommand::FuzzMinimize => minimize_fuzz(path, output),
        ToolCommand::Soundness => emit_soundness(path, output),
        ToolCommand::Playground(address) => run_playground(&address),
        ToolCommand::Snapshots(address, emit_json) => review_snapshots(path, &address, emit_json),
    }
}

fn generate_native_stub(input: &Path, output: Option<&Path>) -> ExitCode {
    let destination = match output {
        Some(path) => path,
        None => return source_less_failure("native-stub requires an output path"),
    };
    match native_stub::generate_file(input, destination) {
        Ok(()) => {
            println!("Generated native surface at '{}'.", destination.display());
            ExitCode::SUCCESS
        }
        Err(message) => source_less_failure(&message),
    }
}

fn current_executable() -> Result<PathBuf, String> {
    std::env::current_exe().map_err(|current_error| format!("cannot locate cinnabar executable: {}", current_error))
}

fn inspect_binary(path: &Path, output: Option<&Path>) -> ExitCode {
    let (root, entry) = match project_or_source(path) {
        Ok(value) => value,
        Err(failure) => return finish_with_manifest_error(&failure),
    };
    let analyzed = analysis::analyze(&entry.to_string_lossy(), &[]);
    if !analyzed.errors.is_empty() {
        return finish_with_diagnostics(&analyzed.errors, &analyzed.notes, &analyzed.files);
    }
    let mut inspected_nodes = analyzed.nodes;
    let mut inspected_lists = analyzed.lists;
    let layouts = match codegen::layout::render_layouts(&analyzed.names, &mut inspected_nodes, &mut inspected_lists) {
        Ok(text) => text,
        Err(codegen_error) => return finish_with_codegen_error(&codegen_error, &analyzed.files),
    };
    let target_dir = root.join("target").join("inspect");
    if let Err(create_error) = std::fs::create_dir_all(&target_dir) {
        return source_less_failure(&format!("cannot create inspection directory: {}", create_error));
    }
    let stem = match entry.file_stem() {
        Some(value) => value,
        None => return source_less_failure("inspection entry has no file stem"),
    };
    let binary = target_dir.join(stem);
    let executable = match current_executable() {
        Ok(value) => value,
        Err(message) => return source_less_failure(&message),
    };
    let compile_status = Command::new(executable).arg(&entry).arg("-o").arg(&binary).status();
    match compile_status {
        Ok(status) => {
            if !status.success() {
                return ExitCode::FAILURE;
            }
        }
        Err(spawn_error) => return source_less_failure(&format!("cannot launch compiler: {}", spawn_error)),
    }
    let report = match advanced_tools::binary_report(&binary, &layouts) {
        Ok(text) => text,
        Err(message) => return source_less_failure(&message),
    };
    match output {
        Some(destination) => match std::fs::write(destination, report) {
            Ok(()) => {
                println!("Wrote binary inspection to '{}'.", destination.display());
                ExitCode::SUCCESS
            }
            Err(write_error) => source_less_failure(&format!("cannot write inspection report: {}", write_error)),
        },
        None => {
            print!("{}", report);
            ExitCode::SUCCESS
        }
    }
}

fn initialize_mushlings(path: &Path) -> ExitCode {
    match advanced_tools::initialize_mushlings(path) {
        Ok(()) => {
            println!("Initialized Mushlings in '{}'.", path.display());
            ExitCode::SUCCESS
        }
        Err(message) => source_less_failure(&message),
    }
}

fn verify_mushlings(path: &Path) -> ExitCode {
    let executable = match current_executable() {
        Ok(value) => value,
        Err(message) => return source_less_failure(&message),
    };
    match advanced_tools::verify_mushlings(path, &executable) {
        Ok((solved, pending, progress)) => {
            for line in progress {
                println!("{}", line);
            }
            println!("Mushlings: {} solved, {} pending.", solved, pending);
            ExitCode::SUCCESS
        }
        Err(message) => source_less_failure(&message),
    }
}

fn replay_fuzz(path: &Path) -> ExitCode {
    let executable = match current_executable() {
        Ok(value) => value,
        Err(message) => return source_less_failure(&message),
    };
    match advanced_tools::replay_fuzz(&executable, path) {
        Ok((passed, diagnostic)) => {
            print!("{}", diagnostic);
            if passed {
                println!("Artifact no longer reproduces a failure.");
                ExitCode::SUCCESS
            } else {
                println!("Artifact deterministically reproduced the failure.");
                ExitCode::FAILURE
            }
        }
        Err(message) => source_less_failure(&message),
    }
}

fn minimize_fuzz(path: &Path, output: Option<&Path>) -> ExitCode {
    let executable = match current_executable() {
        Ok(value) => value,
        Err(message) => return source_less_failure(&message),
    };
    let default_destination = advanced_tools::default_minimized_path(path);
    let destination = match output {
        Some(value) => value,
        None => &default_destination,
    };
    match advanced_tools::minimize_fuzz(&executable, path, destination) {
        Ok(lines) => {
            println!("Minimized artifact to {} lines at '{}'.", lines, destination.display());
            ExitCode::SUCCESS
        }
        Err(message) => source_less_failure(&message),
    }
}

fn emit_soundness(path: &Path, output: Option<&Path>) -> ExitCode {
    let (root, entry) = match project_or_source(path) {
        Ok(value) => value,
        Err(failure) => return finish_with_manifest_error(&failure),
    };
    let analyzed = analysis::analyze(&entry.to_string_lossy(), &[]);
    if !analyzed.errors.is_empty() {
        return finish_with_diagnostics(&analyzed.errors, &analyzed.notes, &analyzed.files);
    }
    let evidence = advanced_tools::soundness_evidence(&entry, &analyzed.nodes, analyzed.errors.len());
    let default_destination = root.join("target").join("soundness-evidence.json");
    let destination = match output {
        Some(value) => value,
        None => &default_destination,
    };
    if let Some(parent) = destination.parent()
        && let Err(create_error) = std::fs::create_dir_all(parent)
    {
        return source_less_failure(&format!("cannot create evidence directory: {}", create_error));
    }
    match std::fs::write(destination, evidence) {
        Ok(()) => {
            println!("Wrote soundness evidence to '{}'.", destination.display());
            ExitCode::SUCCESS
        }
        Err(write_error) => source_less_failure(&format!("cannot write soundness evidence: {}", write_error)),
    }
}

fn run_playground(address: &str) -> ExitCode {
    let executable = match current_executable() {
        Ok(value) => value,
        Err(message) => return source_less_failure(&message),
    };
    println!("Cinnabar playground is available at http://{}", address);
    match advanced_tools::serve_playground(address, &executable, report_source_less) {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => source_less_failure(&message),
    }
}

fn review_snapshots(path: &Path, address: &str, emit_json: bool) -> ExitCode {
    let manifest = match project::discover(path) {
        Ok(value) => value,
        Err(failure) => return finish_with_manifest_error(&failure),
    };
    let executable = match current_executable() {
        Ok(value) => value,
        Err(message) => return source_less_failure(&message),
    };
    if emit_json {
        return match cinnabar::snapshot_review::snapshots_json(&executable, &manifest) {
            Ok(report) => emit_report(&report),
            Err(failure) => finish_with_manifest_error(&failure),
        };
    }
    println!("Cinnabar snapshot review is available at http://{}", address);
    match cinnabar::snapshot_review::serve(address, &executable, &manifest, report_source_less) {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => source_less_failure(&message),
    }
}

fn project_or_source(path: &Path) -> Result<(PathBuf, PathBuf), project::ManifestError> {
    let is_source = path.is_file()
        && path.file_name().and_then(|name| name.to_str()) != Some(project::MANIFEST_FILE)
        && path.extension().and_then(|extension| extension.to_str()) == Some("cnb");
    if is_source {
        let root = match path.parent() {
            Some(parent) => parent.to_path_buf(),
            None => return Err(project::ManifestError::source_less(format!("cannot determine source directory for '{}'", path.display()))),
        };
        return Ok((root, path.to_path_buf()));
    }
    let manifest = project::discover(path)?;
    Ok((manifest.root, manifest.entry))
}

fn generate_documentation(path: &Path, output: Option<&Path>, serve: bool, address: Option<&str>, emit_json: bool) -> ExitCode {
    let (root, entry) = match project_or_source(path) {
        Ok(value) => value,
        Err(failure) => return finish_with_manifest_error(&failure),
    };
    let entry_text = entry.to_string_lossy().to_string();
    let analyzed = analysis::analyze(&entry_text, &[]);
    if !analyzed.errors.is_empty() {
        return report_diagnostics(emit_json, &analyzed.errors, &analyzed.notes, &analyzed.files);
    }
    if emit_json {
        // The document, not a page: a documentation site that wants to lay
        // out its own pages should not have to strip the compiler's.
        return emit_report(&docs::docs_json(
            &analyzed.names,
            &analyzed.nodes,
            &analyzed.lists,
            analyzed.root,
            &analyzed.files,
        ));
    }
    let api_html = docs::render_api_docs(&analyzed.names, &analyzed.nodes, &analyzed.lists, analyzed.root);
    if serve {
        let bind_address = match address {
            Some(value) => value,
            None => return source_less_failure("Cinnabook server address is missing"),
        };
        let page = docs::render_cinnabook(&api_html);
        println!("Cinnabook {} is available at http://{}", env!("CARGO_PKG_VERSION"), bind_address);
        return match docs::serve_cinnabook(bind_address, &page, report_source_less) {
            Ok(()) => ExitCode::SUCCESS,
            Err(message) => source_less_failure(&message),
        };
    }
    let output_dir = match output {
        Some(directory) => directory.to_path_buf(),
        None => root.join("target").join("doc"),
    };
    if let Err(create_error) = std::fs::create_dir_all(&output_dir) {
        return source_less_failure(&format!("cannot create documentation directory '{}': {}", output_dir.display(), create_error));
    }
    let index = output_dir.join("index.html");
    match std::fs::write(&index, api_html) {
        Ok(()) => {
            println!("Generated documentation at '{}'.", index.display());
            ExitCode::SUCCESS
        }
        Err(write_error) => source_less_failure(&format!("cannot write documentation '{}': {}", index.display(), write_error)),
    }
}

fn initialize_project(path: &Path) -> ExitCode {
    match project::initialize(path) {
        Ok(()) => {
            println!("Initialized Cinnabar project in '{}'.", path.display());
            ExitCode::SUCCESS
        }
        Err(failure) => finish_with_manifest_error(&failure),
    }
}

fn run_project_compiler(path: &Path, run: bool, check: bool, target: &str) -> ExitCode {
    if let Err(message) = advanced_tools::validate_target(target) {
        return source_less_failure(&message);
    }
    let manifest = match project::discover(path) {
        Ok(value) => value,
        Err(failure) => return finish_with_manifest_error(&failure),
    };
    let executable = match std::env::current_exe() {
        Ok(value) => value,
        Err(current_error) => return source_less_failure(&format!("cannot locate cinnabar executable: {}", current_error)),
    };
    let mut invocation = Command::new(executable);
    invocation.arg(&manifest.entry);
    invocation.arg("--target").arg(target);
    if check {
        invocation.arg("--check-only");
    } else {
        let output_dir = manifest.root.join("target");
        if let Err(create_error) = std::fs::create_dir_all(&output_dir) {
            return source_less_failure(&format!("cannot create build directory '{}': {}", output_dir.display(), create_error));
        }
        // The artifact is named by the manifest's NAME, not by whichever file
        // happens to be the entry point. A project that renames its entry
        // source is not renaming itself, and NAME is required precisely so
        // there is an answer that does not depend on that.
        invocation.arg("-o").arg(output_dir.join(&manifest.name));
        if run {
            invocation.arg("--run");
        }
    }
    match invocation.status() {
        Ok(status) => exit_code_from_status(status),
        Err(spawn_error) => source_less_failure(&format!("cannot launch compiler: {}", spawn_error)),
    }
}

fn run_project_tests(path: &Path, update_snapshots: bool) -> ExitCode {
    let manifest = match project::discover(path) {
        Ok(value) => value,
        Err(failure) => return finish_with_manifest_error(&failure),
    };
    let executable = match std::env::current_exe() {
        Ok(value) => value,
        Err(current_error) => return source_less_failure(&format!("cannot locate cinnabar executable: {}", current_error)),
    };
    let summary = match project::run_tests(&executable, &manifest, update_snapshots) {
        Ok(value) => value,
        Err(failure) => return finish_with_manifest_error(&failure),
    };
    for failure in &summary.failed {
        eprintln!("FAIL: {}", failure);
    }
    println!("{} passed; {} failed; {} discovered", summary.passed, summary.failed.len(), summary.discovered);
    if summary.failed.is_empty() {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

fn exit_code_from_status(status: std::process::ExitStatus) -> ExitCode {
    if status.success() {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

/// Renders a manifest failure through the reporter every other diagnostic
/// uses. One with a real span shows the offending line of `build.cnb`; one
/// with no Cinnabar origin carries `NO_FILE` and renders source-less, which
/// is what that already means to the reporter.
fn finish_with_manifest_error(failure: &project::ManifestError) -> ExitCode {
    finish_with_diagnostics(&failure.diagnostics, &[], &failure.files)
}

// Renders a source-less runtime error and continues. The server
// subcommands report per-connection failures through this so a bad
// connection is rendered without stopping the listener for later
// visitors; `source_less_failure` below is the same render plus the
// failure exit that fatal tool errors need.
fn report_source_less(message: &str) {
    if let Err(render_error) = render_source_less(message) {
        eprintln!("{}", render_error);
    }
}

fn source_less_failure(message: &str) -> ExitCode {
    report_source_less(message);
    ExitCode::FAILURE
}

fn emit_out_path(args: &CliArgs, ext: &str) -> PathBuf {
    match &args.output {
        Some(path) => path.clone(),
        None => default_out_path(&args.input).with_extension(ext),
    }
}

fn write_output_text(path: &Path, text: &str) -> Result<(), cinnabar::codegen::error::CodegenError> {
    std::fs::write(path, text).map_err(|err| {
        cinnabar::codegen::error::io_error(&format!("cannot write '{}': {}", path.display(), err))
    })
}

fn make_cache(
    files: &[(String, String)],
) -> FnCache<String, impl FnMut(&String) -> Result<String, String>, String> {
    FnCache::new(|path: &String| {
        let mut idx = 0usize;
        while idx < files.len() {
            match files.get(idx) {
                Some((entry_path, text)) => {
                    if entry_path == path {
                        return Ok(text.clone());
                    }
                }
                None => break,
            }
            idx += 1;
        }
        Err(format!("unknown source file '{}'", path))
    })
}

fn file_path_of(files: &[(String, String)], file_id: i64) -> Option<String> {
    files.get(file_id as usize).map(|entry| entry.0.clone())
}

fn render_diagnostics(errors: &[Diag], notes: &[Note], files: &[(String, String)]) -> Result<(), String> {
    let mut cache = make_cache(files);
    let mut idx = 0usize;
    while idx < errors.len() {
        match errors.get(idx) {
            Some(diag) => render_diag(&mut cache, files, diag, notes, idx as i64)?,
            None => break,
        }
        idx += 1;
    }
    Ok(())
}

fn render_source_less(message: &str) -> Result<(), String> {
    Report::build(ReportKind::Error, 0..0)
        .with_message(message)
        .finish()
        .print(Source::from(""))
        .map_err(|render_err| format!("cannot render '{}': {}", message, render_err))
}

fn render_diag(
    cache: &mut FnCache<String, impl FnMut(&String) -> Result<String, String>, String>,
    files: &[(String, String)],
    diag: &Diag,
    notes: &[Note],
    diag_idx: i64,
) -> Result<(), String> {
    if diag.1 == NO_FILE {
        return render_source_less(&diag.0);
    }
    let path = match file_path_of(files, diag.1) {
        Some(path) => path,
        None => {
            return render_source_less(&format!("{} (unknown source file {})", diag.0, diag.1));
        }
    };
    let span = diag.2 as usize..diag.3 as usize;
    let mut report = Report::build(ReportKind::Error, (path.clone(), span.clone()))
        .with_message(&diag.0)
        .with_label(Label::new((path, span)).with_message("here").with_color(Color::Red));
    let mut note_idx = 0usize;
    while note_idx < notes.len() {
        match notes.get(note_idx) {
            Some(note) => {
                if note.0 == diag_idx
                    && note.2 != NO_FILE
                    && let Some(note_path) = file_path_of(files, note.2)
                {
                    report = report.with_label(
                        Label::new((note_path, note.3 as usize..note.4 as usize))
                            .with_message(&note.1)
                            .with_color(Color::Yellow),
                    );
                }
            }
            None => break,
        }
        note_idx += 1;
    }
    report
        .finish()
        .print(&mut *cache)
        .map_err(|render_err| format!("cannot render '{}': {}", diag.0, render_err))
}

fn render_codegen_error(codegen_err: &codegen::error::CodegenError, files: &[(String, String)]) -> Result<(), String> {
    let mut cache = make_cache(files);
    if codegen_err.span.0 == NO_FILE {
        return render_source_less(&codegen_error_message(codegen_err));
    }
    let path = match file_path_of(files, codegen_err.span.0) {
        Some(path) => path,
        None => {
            return render_source_less(&format!(
                "{} (unknown source file {})",
                codegen_error_message(codegen_err),
                codegen_err.span.0
            ));
        }
    };
    let span = codegen_err.span.1 as usize..codegen_err.span.2 as usize;
    let report = Report::build(ReportKind::Error, (path.clone(), span.clone()))
        .with_message(codegen_error_message(codegen_err))
        .with_label(
            Label::new((path, span))
                .with_message("codegen error")
                .with_color(Color::Red),
        )
        .finish();
    report
        .print(&mut cache)
        .map_err(|render_err| format!("cannot render codegen error: {}", render_err))
}

fn entry_span_of(files: &[(String, String)]) -> (i64, i64, i64) {
    match files.first() {
        Some(pair) => (0, 0, pair.1.len() as i64),
        None => (NO_FILE, 0, 0),
    }
}

fn default_out_path(input: &Path) -> PathBuf {
    let text = input.to_string_lossy();
    match text.strip_suffix(".cnb") {
        Some(stripped) => PathBuf::from(stripped),
        None => input.to_path_buf(),
    }
}

fn finish_with_diagnostics(errors: &[Diag], notes: &[Note], files: &[(String, String)]) -> ExitCode {
    if let Err(message) = render_diagnostics(errors, notes, files) {
        let detail = format!("failed to render diagnostic: {}", message);
        if render_source_less(&detail).is_err() {
            return ExitCode::FAILURE;
        }
    }
    ExitCode::FAILURE
}

fn finish_with_diagnostics_json(errors: &[Diag], notes: &[Note], files: &[(String, String)]) -> ExitCode {
    let report = cinnabar::emit_json::diagnostics_report(errors, notes, files);
    match cinnabar::emit_json::render_report(&report) {
        Ok(rendered) => println!("{}", rendered),
        Err(message) => {
            if render_source_less(&message).is_err() {
                return ExitCode::FAILURE;
            }
        }
    }
    ExitCode::FAILURE
}

fn finish_with_codegen_error(codegen_err: &codegen::error::CodegenError, files: &[(String, String)]) -> ExitCode {
    if let Err(message) = render_codegen_error(codegen_err, files) {
        let detail = format!("failed to render diagnostic: {}", message);
        if render_source_less(&detail).is_err() {
            return ExitCode::FAILURE;
        }
    }
    ExitCode::FAILURE
}

fn pad_str(depth: i64) -> String {
    let mut out = String::new();
    let mut idx = 0i64;
    while idx < depth {
        out.push_str("  ");
        idx += 1;
    }
    out
}

fn dump_program(names: &[String], nodes: &[i64], lists: &[Vec<i64>], root: i64) {
    dump_item_list(names, nodes, lists, root, 0);
}

fn dump_item_list(names: &[String], nodes: &[i64], lists: &[Vec<i64>], list: i64, depth: i64) {
    let count = list_len(lists, list);
    let mut idx = 0i64;
    while idx < count {
        dump_item(names, nodes, lists, list_get(lists, list, idx), depth);
        idx += 1;
    }
}

fn path_text(names: &[String], lists: &[Vec<i64>], list: i64) -> String {
    let mut parts: Vec<i64> = Vec::new();
    let count = list_len(lists, list);
    let mut idx = 0i64;
    while idx < count {
        parts.push(list_get(lists, list, idx));
        idx += 1;
    }
    join_path(names, &parts)
}

fn opt_name(names: &[String], id: i64) -> String {
    if id == NONE {
        "none".to_string()
    } else {
        name_text(names, id)
    }
}

fn dump_item(names: &[String], nodes: &[i64], lists: &[Vec<i64>], item: i64, depth: i64) {
    if node_tag(nodes, item) != NODE_ITEM {
        return;
    }
    let pad = pad_str(depth);
    let pub_flag = if node_b(nodes, item) == 1 {
        "is_pub: true"
    } else {
        "is_pub: false"
    };
    let kind = node_a(nodes, item);
    if kind == ITEM_MODULE {
        println!("{}Module({}, name: {}, children:", pad, pub_flag, name_text(names, node_d(nodes, item)));
        dump_item_list(names, nodes, lists, node_e(nodes, item), depth + 1);
        println!("{})", pad);
    } else if kind == ITEM_USE {
        println!(
            "Use({}, path: {}, alias: {})",
            pub_flag,
            path_text(names, lists, node_d(nodes, item)),
            opt_name(names, node_e(nodes, item))
        );
    } else if kind == ITEM_STRUCT {
        println!("{}Struct({}, name: {}, fields:", pad, pub_flag, name_text(names, node_d(nodes, item)));
        dump_field_list(names, nodes, lists, node_e(nodes, item), depth + 1);
        println!("{})", pad);
    } else if kind == ITEM_ENUM {
        println!("{}Enum({}, name: {}, variants:", pad, pub_flag, name_text(names, node_d(nodes, item)));
        dump_variant_list(names, nodes, lists, node_e(nodes, item), depth + 1);
        println!("{})", pad);
    } else if kind == ITEM_TRAIT {
        println!("{}Trait({}, name: {}, methods:", pad, pub_flag, name_text(names, node_d(nodes, item)));
        dump_fn_list(names, nodes, lists, node_e(nodes, item), depth + 1);
        println!("{})", pad);
    } else if kind == ITEM_IMPL {
        println!(
            "{}Impl({}, trait: {}, for: ",
            pad,
            pub_flag,
            path_text(names, lists, node_d(nodes, item))
        );
        dump_ty(names, nodes, lists, node_e(nodes, item), depth + 1);
        println!("{}methods:", pad);
        dump_fn_list(names, nodes, lists, node_f(nodes, item), depth + 1);
        println!("{})", pad);
    } else if kind == ITEM_FUN {
        println!("{}Fun({}, ", pad, pub_flag);
        dump_fn(names, nodes, lists, node_d(nodes, item), depth + 1);
        println!("{})", pad);
    } else if kind == ITEM_NATIVE_FUN {
        println!("{}NativeFun({}, ", pad, pub_flag);
        dump_fn(names, nodes, lists, node_d(nodes, item), depth + 1);
        println!("{})", pad);
    } else if kind == ITEM_CONST {
        println!(
            "{}Const({}, name: {}, ty: ",
            pad,
            pub_flag,
            name_text(names, node_d(nodes, item))
        );
        dump_ty(names, nodes, lists, node_e(nodes, item), depth + 1);
        println!("{}value: ", pad);
        dump_expr(names, nodes, lists, node_f(nodes, item), depth + 1);
        println!("{})", pad);
    } else if kind == ITEM_NATIVE_TYPE {
        println!("{}NativeType({}, name: {})", pad, pub_flag, name_text(names, node_d(nodes, item)));
    }
}

fn dump_field_list(names: &[String], nodes: &[i64], lists: &[Vec<i64>], list: i64, depth: i64) {
    let count = list_len(lists, list);
    let mut idx = 0i64;
    while idx < count {
        let field = list_get(lists, list, idx);
        let pad = pad_str(depth);
        let pub_flag = if node_c(nodes, field) == 1 { "is_pub: true" } else { "is_pub: false" };
        println!("{}Field({}, name: {}, ty: ", pad, pub_flag, name_text(names, node_a(nodes, field)));
        dump_ty(names, nodes, lists, node_b(nodes, field), depth + 1);
        println!("{})", pad);
        idx += 1;
    }
}

fn dump_variant_list(names: &[String], nodes: &[i64], lists: &[Vec<i64>], list: i64, depth: i64) {
    let count = list_len(lists, list);
    let mut idx = 0i64;
    while idx < count {
        let variant = list_get(lists, list, idx);
        let pad = pad_str(depth);
        println!("{}Variant(name: {}, payload:", pad, name_text(names, node_a(nodes, variant)));
        dump_ty_list(names, nodes, lists, node_b(nodes, variant), depth + 1);
        println!("{})", pad);
        idx += 1;
    }
}

fn dump_fn_list(names: &[String], nodes: &[i64], lists: &[Vec<i64>], list: i64, depth: i64) {
    let count = list_len(lists, list);
    let mut idx = 0i64;
    while idx < count {
        dump_fn(names, nodes, lists, list_get(lists, list, idx), depth);
        idx += 1;
    }
}

fn dump_fn(names: &[String], nodes: &[i64], lists: &[Vec<i64>], id: i64, depth: i64) {
    if node_tag(nodes, id) != NODE_FN {
        return;
    }
    let pad = pad_str(depth);
    let impure = if node_e(nodes, id) == 1 { "impure" } else { "pure" };
    println!("{}Fn(name: {}, {}, params:", pad, name_text(names, node_a(nodes, id)), impure);
    dump_param_list(names, nodes, lists, node_c(nodes, id), depth + 1);
    println!("{}ret: ", pad);
    dump_ty(names, nodes, lists, node_d(nodes, id), depth + 1);
    if node_f(nodes, id) != NONE {
        println!("{}body:", pad);
        dump_stmt_list(names, nodes, lists, node_f(nodes, id), depth + 1);
    }
    println!("{})", pad);
}

fn dump_param_list(names: &[String], nodes: &[i64], lists: &[Vec<i64>], list: i64, depth: i64) {
    let count = list_len(lists, list);
    let mut idx = 0i64;
    while idx < count {
        let param = list_get(lists, list, idx);
        let pad = pad_str(depth);
        println!("{}Param(name: {}, ty: ", pad, name_text(names, node_a(nodes, param)));
        dump_ty(names, nodes, lists, node_b(nodes, param), depth + 1);
        println!("{})", pad);
        idx += 1;
    }
}

fn dump_ty_list(names: &[String], nodes: &[i64], lists: &[Vec<i64>], list: i64, depth: i64) {
    let count = list_len(lists, list);
    let mut idx = 0i64;
    while idx < count {
        dump_ty(names, nodes, lists, list_get(lists, list, idx), depth);
        idx += 1;
    }
}

fn dump_ty(names: &[String], nodes: &[i64], lists: &[Vec<i64>], id: i64, depth: i64) {
    if node_tag(nodes, id) != NODE_TY {
        return;
    }
    let pad = pad_str(depth);
    let kind = node_a(nodes, id);
    if kind == TY_NAMED {
        println!("{}Type(Named({}))", pad, name_text(names, node_b(nodes, id)));
    } else if kind == TY_PATH {
        println!("{}Type(Path({}))", pad, path_text(names, lists, node_b(nodes, id)));
    } else if kind == TY_GENERIC {
        println!("{}Type(Generic({}, args: ", pad, path_text(names, lists, node_b(nodes, id)));
        dump_ty_list(names, nodes, lists, node_c(nodes, id), depth + 1);
        println!("{})", pad);
    } else if kind == TY_REF {
        println!("{}Type(Ref(", pad);
        dump_ty(names, nodes, lists, node_b(nodes, id), depth + 1);
        println!("{}))", pad);
    } else if kind == TY_REF_MUT {
        println!("{}Type(RefMut(", pad);
        dump_ty(names, nodes, lists, node_b(nodes, id), depth + 1);
        println!("{}))", pad);
    } else if kind == TY_SLICE {
        println!("{}Type(Slice(", pad);
        dump_ty(names, nodes, lists, node_b(nodes, id), depth + 1);
        println!("{}))", pad);
    } else if kind == TY_ARRAY {
        println!("{}Type(Array(len: {}, elem: ", pad, node_c(nodes, id));
        dump_ty(names, nodes, lists, node_b(nodes, id), depth + 1);
        println!("{}))", pad);
    } else if kind == TY_SELF {
        println!("{}Type(Self)", pad);
    } else if kind == TY_PARAM {
        println!("{}Type(Param({}))", pad, name_text(names, node_b(nodes, id)));
    }
}

fn dump_stmt_list(names: &[String], nodes: &[i64], lists: &[Vec<i64>], list: i64, depth: i64) {
    let count = list_len(lists, list);
    let mut idx = 0i64;
    while idx < count {
        dump_stmt(names, nodes, lists, list_get(lists, list, idx), depth);
        idx += 1;
    }
}

fn dump_stmt(names: &[String], nodes: &[i64], lists: &[Vec<i64>], id: i64, depth: i64) {
    if node_tag(nodes, id) != NODE_STMT {
        return;
    }
    let pad = pad_str(depth);
    let kind = node_a(nodes, id);
    if kind == STMT_LET {
        println!(
            "{}Let(mut: {}, name: {}, ty: ",
            pad,
            node_b(nodes, id),
            name_text(names, node_c(nodes, id))
        );
        if node_d(nodes, id) != NONE {
            dump_ty(names, nodes, lists, node_d(nodes, id), depth + 1);
        }
        println!("{}init: ", pad);
        dump_expr(names, nodes, lists, node_e(nodes, id), depth + 1);
        println!("{})", pad);
    } else if kind == STMT_ASSIGN {
        println!("{}Assign(target: ", pad);
        dump_expr(names, nodes, lists, node_b(nodes, id), depth + 1);
        println!("{}value: ", pad);
        dump_expr(names, nodes, lists, node_c(nodes, id), depth + 1);
        println!("{})", pad);
    } else if kind == STMT_WHILE {
        println!("{}While(cond: ", pad);
        dump_expr(names, nodes, lists, node_b(nodes, id), depth + 1);
        println!("{}body:", pad);
        dump_stmt_list(names, nodes, lists, node_c(nodes, id), depth + 1);
        println!("{})", pad);
    } else if kind == STMT_IF {
        println!("{}If(cond: ", pad);
        dump_expr(names, nodes, lists, node_b(nodes, id), depth + 1);
        println!("{}then:", pad);
        dump_stmt_list(names, nodes, lists, node_c(nodes, id), depth + 1);
        if node_d(nodes, id) != NONE {
            println!("{}else:", pad);
            dump_stmt_list(names, nodes, lists, node_d(nodes, id), depth + 1);
        }
        println!("{})", pad);
    } else if kind == STMT_RETURN {
        println!("{}Return(value: ", pad);
        if node_b(nodes, id) != NONE {
            dump_expr(names, nodes, lists, node_b(nodes, id), depth + 1);
        }
        println!("{})", pad);
    } else if kind == STMT_BREAK {
        println!("{}Break", pad);
    } else if kind == STMT_CONTINUE {
        println!("{}Continue", pad);
    } else if kind == STMT_EXPR {
        println!("{}ExprStmt(", pad);
        dump_expr(names, nodes, lists, node_b(nodes, id), depth + 1);
        println!("{})", pad);
    }
}

fn dump_expr_list(names: &[String], nodes: &[i64], lists: &[Vec<i64>], list: i64, depth: i64) {
    let count = list_len(lists, list);
    let mut idx = 0i64;
    while idx < count {
        dump_expr(names, nodes, lists, list_get(lists, list, idx), depth);
        idx += 1;
    }
}

fn dump_expr(names: &[String], nodes: &[i64], lists: &[Vec<i64>], id: i64, depth: i64) {
    if node_tag(nodes, id) != NODE_EXPR {
        return;
    }
    let pad = pad_str(depth);
    let kind = node_a(nodes, id);
    if kind == EXPR_LIT {
        let lit = node_b(nodes, id);
        if lit == LIT_STRING {
            // A string literal's `c` slot is the interned name id of its
            // decoded bytes, not a number, so the dump shows the bytes.
            println!("{}Lit(string, \"{}\")", pad, escaped_literal_text(&name_text(names, node_c(nodes, id))));
        } else {
            println!("{}Lit({}, {})", pad, lit_kind_name(lit), node_c(nodes, id));
        }
    } else if kind == EXPR_PATH {
        println!("{}Path({})", pad, path_text(names, lists, node_b(nodes, id)));
    } else if kind == EXPR_UNARY {
        println!("{}Unary({}, ", pad, unary_name(node_b(nodes, id)));
        dump_expr(names, nodes, lists, node_c(nodes, id), depth + 1);
        println!("{})", pad);
    } else if kind == EXPR_BINARY {
        println!("{}Binary({}, lhs: ", pad, bin_name(node_b(nodes, id)));
        dump_expr(names, nodes, lists, node_c(nodes, id), depth + 1);
        println!("{}rhs: ", pad);
        dump_expr(names, nodes, lists, node_d(nodes, id), depth + 1);
        println!("{})", pad);
    } else if kind == EXPR_CALL {
        println!("{}Call(callee: ", pad);
        dump_expr(names, nodes, lists, node_b(nodes, id), depth + 1);
        println!("{}args:", pad);
        dump_expr_list(names, nodes, lists, node_d(nodes, id), depth + 1);
        println!("{})", pad);
    } else if kind == EXPR_STRUCT_LIT {
        println!("{}StructLit({}, fields: ", pad, path_text(names, lists, node_b(nodes, id)));
        let names_list = node_c(nodes, id);
        let values_list = node_d(nodes, id);
        let count = list_len(lists, names_list);
        let mut idx = 0i64;
        while idx < count {
            println!("{}{}: ", pad, name_text(names, list_get(lists, names_list, idx)));
            dump_expr(names, nodes, lists, list_get(lists, values_list, idx), depth + 1);
            idx += 1;
        }
        println!("{})", pad);
    } else if kind == EXPR_ARRAY {
        println!("{}Array(elems:", pad);
        dump_expr_list(names, nodes, lists, node_b(nodes, id), depth + 1);
        println!("{})", pad);
    } else if kind == EXPR_MATCH {
        println!("{}Match(scrutinee: ", pad);
        dump_expr(names, nodes, lists, node_b(nodes, id), depth + 1);
        println!("{}arms:", pad);
        dump_arm_list(names, nodes, lists, node_c(nodes, id), depth + 1);
        println!("{})", pad);
    } else if kind == EXPR_TRY {
        println!("{}Try(", pad);
        dump_expr(names, nodes, lists, node_b(nodes, id), depth + 1);
        println!("{})", pad);    } else if kind == EXPR_INDEX {
        println!("{}Index(base:", pad);
        dump_expr(names, nodes, lists, node_b(nodes, id), depth + 1);
        println!("{}index: ", pad);
        dump_expr(names, nodes, lists, node_c(nodes, id), depth + 1);
        println!("{})", pad);
    } else if kind == EXPR_FIELD_ACCESS {
        println!("{}FieldAccess(base: ", pad);
        dump_expr(names, nodes, lists, node_b(nodes, id), depth + 1);
        println!("{}.{})", pad, name_text(names, node_c(nodes, id)));
    }
}

fn dump_arm_list(names: &[String], nodes: &[i64], lists: &[Vec<i64>], list: i64, depth: i64) {
    let count = list_len(lists, list);
    let mut idx = 0i64;
    while idx < count {
        let arm = list_get(lists, list, idx);
        let pad = pad_str(depth);
        println!("{}Arm(pattern: ", pad);
        dump_pat(names, nodes, lists, node_a(nodes, arm), depth + 1);
        println!("{}body:", pad);
        dump_stmt_list(names, nodes, lists, node_b(nodes, arm), depth + 1);
        println!("{})", pad);
        idx += 1;
    }
}

fn dump_pat_list(names: &[String], nodes: &[i64], lists: &[Vec<i64>], list: i64, depth: i64) {
    let count = list_len(lists, list);
    let mut idx = 0i64;
    while idx < count {
        dump_pat(names, nodes, lists, list_get(lists, list, idx), depth);
        idx += 1;
    }
}

fn dump_pat(names: &[String], nodes: &[i64], lists: &[Vec<i64>], id: i64, depth: i64) {
    if node_tag(nodes, id) != NODE_PAT {
        return;
    }
    let pad = pad_str(depth);
    let kind = node_a(nodes, id);
    if kind == PAT_BIND {
        println!("{}Bind({})", pad, name_text(names, node_b(nodes, id)));
    } else if kind == PAT_PATH {
        println!("{}PatPath({})", pad, path_text(names, lists, node_b(nodes, id)));
    } else if kind == PAT_VARIANT {
        println!("{}PatVariant({}, payload:", pad, path_text(names, lists, node_b(nodes, id)));
        dump_pat_list(names, nodes, lists, node_c(nodes, id), depth + 1);
        println!("{})", pad);
    } else if kind == PAT_ARRAY {
        println!("{}PatArray(elems:", pad);
        dump_pat_list(names, nodes, lists, node_b(nodes, id), depth + 1);
        if node_c(nodes, id) != NONE {
            println!("{}rest: {}", pad, name_text(names, node_c(nodes, id)));
        }
        println!("{})", pad);
    } else if kind == PAT_LIT {
        println!("{}PatLit({}, {})", pad, lit_kind_name(node_b(nodes, id)), node_c(nodes, id));
    }
}

// The literal kinds an `EXPR_LIT` node's `b` slot holds.  These are `LIT_*`
// values, not the `TOK_*` token kinds the lexer produced them from; the two
// numberings do not line up.
fn lit_kind_name(kind: i64) -> &'static str {
    if kind == LIT_INT {
        "int"
    } else if kind == LIT_HEX {
        "hex"
    } else if kind == LIT_TRUE {
        "true"
    } else if kind == LIT_FALSE {
        "false"
    } else if kind == LIT_STRING {
        "string"
    } else {
        "?lit"
    }
}

fn unary_name(op: i64) -> &'static str {
    if op == UN_NEG {
        "neg"
    } else if op == UN_NOT {
        "not"
    } else if op == UN_REF {
        "ref"
    } else if op == UN_REF_MUT {
        "ref_mut"
    } else {
        "?un"
    }
}

fn bin_name(op: i64) -> &'static str {
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
    } else if op == BIN_OR {
        "||"
    } else {
        "?bin"
    }
}

fn run_binary(path: &Path) -> ExitCode {
    // A separator-less program name — the default output for `main.cnb`
    // compiled in its own directory — would make `Command::new` search
    // `$PATH` instead of running the binary that was just built, silently
    // executing whatever else happens to be called `main`. Qualifying it
    // with the current directory makes it unambiguously a path to this
    // file. The name on disk is unchanged; only the invocation is.
    let invoked = if path.parent().is_some_and(|parent| !parent.as_os_str().is_empty()) {
        path.to_path_buf()
    } else {
        Path::new(".").join(path)
    };
    match Command::new(&invoked).status() {
        Ok(status) => match status.code() {
            Some(code) => {
                if code == 0 {
                    ExitCode::SUCCESS
                } else {
                    ExitCode::FAILURE
                }
            }
            None => ExitCode::FAILURE,
        },
        Err(err) => {
            eprintln!("failed to execute '{}': {}", invoked.display(), err);
            ExitCode::FAILURE
        }
    }
}
