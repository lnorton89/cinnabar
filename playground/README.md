# The hosted Cinnabar playground

A server that compiles, links, and **runs** what you type, and shows you
everything the compiler established on the way: diagnostics with their
explanations, the parse-only arena, the arena with every attached fact, the ABI
layout, the LLVM IR, and the program's own output and exit status.

This is a different thing from the in-browser playground on the site
(`site/src/app/playground/`, backed by `crates/cinnabar-wasm`). That one runs
the front end in your browser and cannot execute anything, because code
generation needs LLVM and a linker. This one has both, which is why it needs a
container around it.

```
playground/
  server/    the API: runs the compiler, shapes what it said
  web/       the editor and the tabs
  Containerfile
  compose.playground.yaml
```

## Running it

```bash
cd playground/web && npm install && npm run build   # the front end is served as static files
cd ../.. && docker compose -f playground/compose.playground.yaml up --build
```

It binds `127.0.0.1:8080`. Put a TLS-terminating reverse proxy in front rather
than publishing the container port straight onto an interface.

For development, run the two halves separately — the Vite dev server proxies
`/api` to the API:

```bash
cd playground/server && CINNABAR_BIN=../../target/debug/cinnabar npm start
cd playground/web && npm run dev
```

## The sandbox is the container, not the API

This service exists to execute code written by strangers. That is the whole
feature, and it is also the whole risk, so it is worth being exact about which
part of this directory contains it.

**The API bounds how much work one visitor can ask for.** A submission is capped
at 64 KiB, each compiler invocation at 10 seconds, each program run at 5 seconds,
captured output at 64 KiB per stream, and the service refuses a submission
outright once four are already in flight rather than queueing it. Scratch
directories are unique per submission and removed whatever happened. Static file
paths containing a `..` segment are refused rather than normalized.

**None of that constrains what a program can do once it runs.** A program that
opens a socket, reads a file, or forks is not stopped by any of the above. What
stops it is the runtime configuration in `compose.playground.yaml`:

| Setting | What it prevents |
|---|---|
| `network_mode: none` | A submitted program cannot call out, be called, or reach anything else in the project |
| `read_only: true` + `tmpfs` | Nothing a build writes outlives the container; the image itself cannot be modified |
| `cap_drop: ALL`, `no-new-privileges` | A program runs with no capabilities and cannot acquire any |
| `pids_limit`, `ulimits.nproc` | Fork bombs terminate instead of taking the host down |
| `mem_limit`, `memswap_limit` | Runaway allocation is bounded |
| `cpus` | One submission cannot spend the whole machine |
| `ulimits.fsize` | A program cannot fill the tmpfs |
| non-root `USER` in the image | Nothing above depends on the daemon having been asked nicely |

**Running the image without those options means running arbitrary code with the
daemon's defaults.** If you deploy this some other way — Kubernetes, a systemd
unit, a different runtime — reproduce every row of that table before it takes
its first submission. The API cannot tell whether you did, and it will happily
serve either way.

One deliberate gap: `/tmp` is mounted `nosuid,nodev` but **not** `noexec`,
because executing the compiled program is the point. That is the one place a
submission's own code runs, and it is why every other row of the table matters.

## What the API returns

`POST /api/compile` with `{"source": "...", "execute": true}` answers with one
document:

```json
{
  "format": "cinnabar.playground.v1",
  "accepted": true,
  "diagnostics": { "ok": true, "document": { "format": "cinnabar.diagnostics.v1", "…": "…" } },
  "ast":        { "ok": true, "document": { "format": "cinnabar.ast.v1", "…": "…" } },
  "typedAst":   { "ok": true, "document": { "format": "cinnabar.typed-ast.v1", "…": "…" } },
  "layout":     { "ok": true, "document": { "format": "cinnabar.layout.v1", "…": "…" } },
  "llvmIr":     { "ok": true, "text": "…" },
  "program":    { "ok": true, "exitCode": 0, "stdout": "", "stderr": "", "truncated": false }
}
```

Every section except `program` is a compiler `--emit-json` document, passed
through rather than summarized. The playground cannot tell you something a real
build would not, because it is not doing its own analysis — that is what makes
it worth trusting as a way to learn the language.

A rejected program gets `accepted: false`, its diagnostics, and its parse-only
arena — parsing succeeded, which is why the AST tab still has something in it —
and `null` for everything that only exists once the front end passes.

`GET /api/health` reports the limits a client has to respect. `GET /api/examples`
returns the example corpus.

## Tests

```bash
cd playground/server && npm test
```

The suite covers what a reader should not have to take on faith: that a climbing
path is refused, that an oversized submission is refused rather than compiled,
that the concurrency cap refuses rather than queues, that a rejected program
still reports diagnostics and a parse tree, that an accepted one reports a
layout matching what the compiler measured, and that a program which never
finishes is killed rather than waited on.
