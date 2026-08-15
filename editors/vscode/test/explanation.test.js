const test = require("node:test");
const assert = require("node:assert");
const { renderExplanationHtml, layoutExplanations, describeLocation } = require("../explanation");

const LOCATION = {
  uri: "file:///work/project/main.cnb",
  range: { start: { line: 17, character: 2 }, end: { line: 17, character: 24 } }
};

// The shape `cinnabar-lsp` sends with a code lens: a linear value bound in
// one place, consumed on one branch and left live on another.
const JOIN_FAILURE = {
  format: "cinnabar.explanation.v1",
  diagnostic: { message: "'block' is consumed on some paths but not others", location: LOCATION },
  explanations: [
    { kind: "consumed", message: "'block' is consumed by the end of this path", location: LOCATION },
    { kind: "live", message: "'block' is still live at the end of this path", location: LOCATION },
    { kind: "binding", message: "'block' is bound here with linear type 'Memory.Block'", location: LOCATION }
  ],
  focus: 0
};

test("the binding leads and the disagreeing paths become parallel lanes", () => {
  const { trunkBefore, branches, trunkAfter } = layoutExplanations(JOIN_FAILURE.explanations);
  assert.deepStrictEqual(
    trunkBefore.map((node) => node.kind),
    ["binding"]
  );
  assert.deepStrictEqual(
    branches.map((node) => node.kind),
    ["consumed", "live"]
  );
  assert.deepStrictEqual(trunkAfter, []);
});

test("guidance is placed last whatever order the checker raised it in", () => {
  const { trunkBefore, trunkAfter } = layoutExplanations([
    { kind: "guidance", message: "consume the existing value first", location: LOCATION },
    { kind: "binding", message: "bound here", location: LOCATION }
  ]);
  assert.deepStrictEqual(
    trunkBefore.map((node) => node.kind),
    ["binding"]
  );
  assert.deepStrictEqual(
    trunkAfter.map((node) => node.kind),
    ["guidance"]
  );
});

test("every explanation keeps the index the host reveals it by", () => {
  const { trunkBefore, branches } = layoutExplanations(JOIN_FAILURE.explanations);
  const indices = [...trunkBefore, ...branches].map((node) => node.index).sort();
  // Reordering for the diagram must not renumber the nodes: the host looks
  // the clicked node up in the array the server sent.
  assert.deepStrictEqual(indices, [0, 1, 2]);
});

test("an unrecognized kind is shown rather than dropped", () => {
  const { trunkBefore } = layoutExplanations([{ kind: "something-new", message: "note", location: LOCATION }]);
  assert.strictEqual(trunkBefore.length, 1);
  const html = renderExplanationHtml({ explanations: [{ kind: "something-new", message: "note" }] }, "abc");
  assert.ok(html.includes("note"));
});

test("a location renders as file and one-based line", () => {
  assert.strictEqual(describeLocation(LOCATION), "main.cnb:18");
  assert.strictEqual(describeLocation(undefined), "");
});

test("the document carries a nonce-scoped policy and loads nothing remote", () => {
  const html = renderExplanationHtml(JOIN_FAILURE, "test-nonce");
  assert.ok(html.includes("script-src 'nonce-test-nonce'"));
  assert.ok(html.includes('<script nonce="test-nonce">'));
  assert.ok(html.includes("default-src 'none'"));
  // A webview that reached the network would be a surprise from a panel
  // that only ever displays what the compiler already said.
  assert.ok(!/src=["']https?:/.test(html));
});

test("a message that looks like markup is shown, not interpreted", () => {
  const html = renderExplanationHtml(
    {
      diagnostic: { message: "<img src=x onerror=alert(1)>" },
      explanations: [{ kind: "binding", message: "'<b>x</b>' is bound here", location: LOCATION }]
    },
    "nonce"
  );
  assert.ok(!html.includes("<img src=x"));
  assert.ok(html.includes("&lt;img src=x"));
  assert.ok(html.includes("&lt;b&gt;x&lt;/b&gt;"));
});

test("a diagnostic with no explanations says so instead of drawing an empty diagram", () => {
  const html = renderExplanationHtml({ diagnostic: { message: "some error" }, explanations: [] }, "nonce");
  assert.ok(html.includes("attached no explanation"));
  assert.ok(!html.includes('class="lanes"'));
});

test("a node with no location is not offered as somewhere to jump", () => {
  const html = renderExplanationHtml(
    { explanations: [{ kind: "guidance", message: "do the thing" }] },
    "nonce"
  );
  assert.ok(html.includes("disabled"));
});

test("the focused note is marked so the clicked lens is findable in the diagram", () => {
  const html = renderExplanationHtml(JOIN_FAILURE, "nonce");
  assert.ok(html.includes("node--focus"));
  assert.ok(html.includes('data-index="0"'));
});
