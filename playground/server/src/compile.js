// Running the compiler over a submission, and shaping what it said.
//
// Every answer this service gives comes from the compiler's own
// `--emit-json` documents rather than from parsing its terminal output, so
// the playground cannot report something a real build would not. The one
// exception is the program's own stdout and stderr, which are the program's
// and not the compiler's.
//
// The limits here are the request-shaped ones: how large a submission may
// be, how long a stage may run, how long a program may run, and how much of
// its output is kept. They are necessary and they are not sufficient — a
// submission is arbitrary code, and the boundary that actually contains it
// is the container described in `playground/README.md`. Nothing in this
// file should be read as a sandbox.

import { execFile } from "node:child_process";
import { mkdtemp, rm, writeFile, readFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";

/** The largest submission accepted, in bytes. */
export const MAX_SOURCE_BYTES = 64 * 1024;

/** How long any one compiler invocation may run. */
export const STAGE_TIMEOUT_MS = 10_000;

/** How long a compiled program may run before it is killed. */
export const RUN_TIMEOUT_MS = 5_000;

/** How much of a program's output is kept, in bytes, per stream. */
export const MAX_OUTPUT_BYTES = 64 * 1024;

/**
 * How large a compiler document may be.
 *
 * Far larger than a program's output cap, and deliberately so: the typed
 * arena for even a short program is every node the compiler allocated, and
 * capping it at a submission's size would silently truncate the tab whose
 * whole point is completeness.
 */
export const MAX_DOCUMENT_BYTES = 32 * 1024 * 1024;

/** The name a submission is compiled under, and so the name in its spans. */
const ENTRY_NAME = "playground.cnb";

/**
 * Run one command to completion, capturing both streams.
 *
 * A non-zero exit is an outcome, not a failure to run: a rejected program
 * is the most interesting thing this service reports. Only being unable to
 * start the process, or the timeout, is an error.
 */
function run(command, args, { timeout, cwd, maxBuffer = MAX_OUTPUT_BYTES }) {
  return new Promise((resolve, reject) => {
    execFile(
      command,
      args,
      { timeout, cwd, maxBuffer, killSignal: "SIGKILL", encoding: "utf8" },
      (error, stdout, stderr) => {
        if (error && error.killed) {
          reject(new Error(`timed out after ${timeout} ms`));
          return;
        }
        if (error && error.code === undefined && !error.killed) {
          reject(new Error(error.message));
          return;
        }
        resolve({ code: error ? error.code ?? 1 : 0, stdout, stderr });
      },
    );
  });
}

/**
 * Parse one `--emit-json` document.
 *
 * A document that does not parse is reported as such rather than thrown
 * away: it means the compiler and this service disagree about a surface,
 * which is worth seeing rather than hiding behind an empty tab.
 */
function parseDocument(stdout, stderr) {
  const text = stdout.trim();
  if (text === "") {
    return { ok: false, error: stderr.trim() || "the compiler produced no document" };
  }
  try {
    return { ok: true, document: JSON.parse(text) };
  } catch (failure) {
    return { ok: false, error: `the compiler's document did not parse: ${failure.message}` };
  }
}

async function emitJson(compiler, directory, entry, flags) {
  const result = await run(compiler, [entry, ...flags, "--emit-json"], {
    timeout: STAGE_TIMEOUT_MS,
    cwd: directory,
    maxBuffer: MAX_DOCUMENT_BYTES,
  });
  return parseDocument(result.stdout, result.stderr);
}

function truncate(text) {
  if (text.length <= MAX_OUTPUT_BYTES) {
    return { text, truncated: false };
  }
  return { text: text.slice(0, MAX_OUTPUT_BYTES), truncated: true };
}

/**
 * Compile a submission and report everything the compiler established
 * about it.
 *
 * `execute` decides whether the program is run after a successful build.
 * The front end asks for it explicitly, because running a program is a
 * different thing from being told whether it compiles and a reader should
 * not have to guess which one they got.
 */
export async function compileSubmission({ compiler, source, execute = false }) {
  if (typeof source !== "string") {
    throw new Error("a submission must be source text");
  }
  const bytes = Buffer.byteLength(source, "utf8");
  if (bytes > MAX_SOURCE_BYTES) {
    throw new Error(`submission is ${bytes} bytes; the limit is ${MAX_SOURCE_BYTES}`);
  }

  const directory = await mkdtemp(join(tmpdir(), "cinnabar-playground-"));
  const entry = join(directory, ENTRY_NAME);
  try {
    await writeFile(entry, source, "utf8");

    // Diagnostics first, and on their own: everything below is only worth
    // asking for if the front end passed, and reporting a stale AST beside
    // a fresh error would be worse than reporting nothing.
    const diagnostics = await emitJson(compiler, directory, entry, ["--check-only"]);
    const accepted =
      diagnostics.ok && Array.isArray(diagnostics.document.diagnostics) && diagnostics.document.diagnostics.length === 0;

    // The parse-only arena is available even for a program the front end
    // rejects — that is the point of stopping after parsing — so it is
    // fetched either way.
    const ast = await emitJson(compiler, directory, entry, ["--dump-ast"]);

    const response = {
      format: "cinnabar.playground.v1",
      accepted,
      diagnostics,
      ast,
      typedAst: null,
      layout: null,
      llvmIr: null,
      program: null,
    };

    if (!accepted) {
      return response;
    }

    response.typedAst = await emitJson(compiler, directory, entry, ["--dump-typed-ast"]);
    response.layout = await emitJson(compiler, directory, entry, ["--print-layout"]);

    const irPath = join(directory, "playground.ll");
    const emitted = await run(compiler, [entry, "--emit-llvm", "-o", irPath], {
      timeout: STAGE_TIMEOUT_MS,
      cwd: directory,
      maxBuffer: MAX_DOCUMENT_BYTES,
    });
    response.llvmIr =
      emitted.code === 0
        ? { ok: true, text: truncate(await readFile(irPath, "utf8")).text }
        : { ok: false, error: (emitted.stderr || emitted.stdout).trim() };

    if (!execute) {
      return response;
    }

    const binary = join(directory, "playground");
    const built = await run(compiler, [entry, "-o", binary], { timeout: STAGE_TIMEOUT_MS, cwd: directory });
    if (built.code !== 0) {
      response.program = { ok: false, error: (built.stderr || built.stdout).trim() };
      return response;
    }
    try {
      const executed = await run(binary, [], { timeout: RUN_TIMEOUT_MS, cwd: directory });
      const stdout = truncate(executed.stdout);
      const stderr = truncate(executed.stderr);
      response.program = {
        ok: true,
        exitCode: executed.code,
        stdout: stdout.text,
        stderr: stderr.text,
        truncated: stdout.truncated || stderr.truncated,
      };
    } catch (failure) {
      response.program = { ok: false, error: failure.message };
    }
    return response;
  } finally {
    // The scratch directory goes whatever happened. A submission is
    // somebody else's code and it does not get to leave anything behind.
    await rm(directory, { recursive: true, force: true });
  }
}
