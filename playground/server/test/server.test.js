import test from "node:test";
import assert from "node:assert";
import { once } from "node:events";
import { join, resolve } from "node:path";
import { createPlaygroundServer, staticPathFor } from "../src/server.js";
import { compileSubmission, MAX_SOURCE_BYTES } from "../src/compile.js";
import { EXAMPLES } from "../src/examples.js";

const repoRoot = resolve(import.meta.dirname, "..", "..", "..");
const compiler = process.env.CINNABAR_BIN || join(repoRoot, "target", "debug", "cinnabar");

async function withServer(options, body) {
  const server = createPlaygroundServer({ compiler, ...options });
  server.listen(0, "127.0.0.1");
  await once(server, "listening");
  const { port } = server.address();
  try {
    return await body(`http://127.0.0.1:${port}`);
  } finally {
    server.close();
    await once(server, "close");
  }
}

test("a path that climbs out of the static root is refused", () => {
  const root = "/srv/web";
  assert.strictEqual(staticPathFor(root, "/index.html"), resolve("/srv/web/index.html"));
  assert.strictEqual(staticPathFor(root, "/"), resolve("/srv/web/index.html"));
  // Both spellings of the climb, and the encoded one, have to land nowhere.
  assert.strictEqual(staticPathFor(root, "/../../etc/passwd"), null);
  assert.strictEqual(staticPathFor(root, "/%2e%2e/%2e%2e/etc/passwd"), null);
  assert.strictEqual(staticPathFor(root, "/assets/../../etc/passwd"), null);
});

test("health reports the limits a client has to respect", async () => {
  await withServer({}, async (base) => {
    const response = await fetch(`${base}/api/health`);
    assert.strictEqual(response.status, 200);
    const body = await response.json();
    assert.strictEqual(body.ok, true);
    assert.strictEqual(body.maxSourceBytes, MAX_SOURCE_BYTES);
    assert.ok(body.maxConcurrent >= 1);
  });
});

test("the example corpus is served and every example carries source", async () => {
  await withServer({}, async (base) => {
    const body = await (await fetch(`${base}/api/examples`)).json();
    assert.strictEqual(body.examples.length, EXAMPLES.length);
    for (const example of body.examples) {
      assert.ok(example.id && example.title && example.blurb);
      assert.ok(example.source.trim().length > 0, `${example.id} has no source`);
    }
  });
});

test("a submission past the size cap is refused rather than compiled", async () => {
  await withServer({}, async (base) => {
    const response = await fetch(`${base}/api/compile`, {
      method: "POST",
      body: JSON.stringify({ source: "#".repeat(MAX_SOURCE_BYTES + 4096) }),
    });
    assert.strictEqual(response.status, 400);
    const body = await response.json();
    assert.match(body.error, /exceeds|limit/);
  });
});

test("a body that is not JSON is refused", async () => {
  await withServer({}, async (base) => {
    const response = await fetch(`${base}/api/compile`, { method: "POST", body: "not json" });
    assert.strictEqual(response.status, 400);
  });
});

test("more submissions than the concurrency cap get a refusal, not a queue", async () => {
  // With the cap at one, the second request must be told to come back
  // rather than be held: an unbounded queue turns one slow submission into
  // everyone's slow submission.
  await withServer({ maxConcurrent: 1 }, async (base) => {
    const slow = fetch(`${base}/api/compile`, {
      method: "POST",
      body: JSON.stringify({ source: EXAMPLES[0].source, execute: true }),
    });
    const statuses = [];
    for (let attempt = 0; attempt < 12; attempt += 1) {
      const response = await fetch(`${base}/api/compile`, {
        method: "POST",
        body: JSON.stringify({ source: EXAMPLES[0].source }),
      });
      statuses.push(response.status);
      await response.json();
      if (response.status === 503) {
        break;
      }
    }
    await slow.then((response) => response.json());
    assert.ok(statuses.includes(503), `expected a refusal, saw ${statuses.join(", ")}`);
  });
});

test("a rejected program reports the compiler's diagnostics and its parse tree", async (t) => {
  const rejected = EXAMPLES.find((example) => example.id === "immutable-binding");
  let result;
  try {
    result = await compileSubmission({ compiler, source: rejected.source });
  } catch (failure) {
    t.skip(`compiler not available: ${failure.message}`);
    return;
  }
  assert.strictEqual(result.accepted, false);
  assert.ok(result.diagnostics.ok, "diagnostics document did not parse");
  assert.ok(result.diagnostics.document.diagnostics.length > 0);
  // Parsing succeeded even though the front end rejected the program, so
  // the AST tab has something real in it rather than being blank.
  assert.ok(result.ast.ok, "the parse-only arena should still be available");
  assert.strictEqual(result.typedAst, null, "a rejected program has no attached facts to show");
  assert.strictEqual(result.program, null);
});

test("an accepted program reports facts, IR, and its own exit status", async (t) => {
  const accepted = EXAMPLES.find((example) => example.id === "struct-layout");
  let result;
  try {
    result = await compileSubmission({ compiler, source: accepted.source, execute: true });
  } catch (failure) {
    t.skip(`compiler not available: ${failure.message}`);
    return;
  }
  assert.strictEqual(result.accepted, true, JSON.stringify(result.diagnostics));
  assert.strictEqual(result.diagnostics.document.diagnostics.length, 0);
  assert.strictEqual(result.typedAst.document.format, "cinnabar.typed-ast.v1");
  assert.strictEqual(result.layout.document.format, "cinnabar.layout.v1");
  const point = result.layout.document.types.find((entry) => entry.type === "Point");
  assert.ok(point, "the declared struct should appear in the layout report");
  assert.strictEqual(point.size, 16);
  assert.ok(result.llvmIr.ok && result.llvmIr.text.includes("define"));
  assert.ok(result.program.ok, JSON.stringify(result.program));
  assert.strictEqual(result.program.exitCode, 0);
});

test("a program that never finishes is killed rather than waited on", async (t) => {
  const spinner = `pub fun main() I64
  var count: I64 = 0
  while count == 0
  end
  return 0
end
`;
  let result;
  try {
    result = await compileSubmission({ compiler, source: spinner, execute: true });
  } catch (failure) {
    t.skip(`compiler not available: ${failure.message}`);
    return;
  }
  assert.strictEqual(result.accepted, true, JSON.stringify(result.diagnostics));
  assert.strictEqual(result.program.ok, false);
  assert.match(result.program.error, /timed out/);
});
