const test = require("node:test");
const assert = require("node:assert");
const path = require("node:path");
const { TASK_TEMPLATES, findProjectRoot, createTaskSpecs, quoteCommandLine } = require("../tasks");

// A fake filesystem: the set of paths that exist, so the selection rules can
// be exercised without writing manifests to disk.
function existsIn(paths) {
  const present = new Set(paths.map((entry) => path.resolve(entry)));
  return (candidate) => present.has(path.resolve(candidate));
}

test("a manifest above the opened folder still names the project", () => {
  const root = findProjectRoot("/work/project/src/deep", existsIn(["/work/project/build.cnb"]));
  assert.strictEqual(root, path.resolve("/work/project"));
});

test("a folder with no manifest anywhere above it has no project", () => {
  assert.strictEqual(findProjectRoot("/work/elsewhere", existsIn([])), undefined);
});

test("the nearest manifest wins over one further up", () => {
  const exists = existsIn(["/work/build.cnb", "/work/inner/build.cnb"]);
  assert.strictEqual(findProjectRoot("/work/inner/src", exists), path.resolve("/work/inner"));
});

test("every template becomes a task for a detected project", () => {
  const specs = createTaskSpecs({
    workspaceFolders: ["/work/project"],
    executable: "cinnabar",
    pathExists: existsIn(["/work/project/build.cnb"])
  });
  assert.strictEqual(specs.length, TASK_TEMPLATES.length);
  assert.deepStrictEqual(
    specs.map((spec) => spec.name),
    TASK_TEMPLATES.map((template) => template.name)
  );
  for (const spec of specs) {
    assert.strictEqual(spec.cwd, path.resolve("/work/project"));
    // Each command is handed the project path explicitly, so the task does
    // not depend on where the terminal happened to open.
    assert.strictEqual(spec.args[spec.args.length - 1], path.resolve("/work/project"));
  }
});

test("a workspace with no project contributes no tasks", () => {
  const specs = createTaskSpecs({
    workspaceFolders: ["/work/notes"],
    executable: "cinnabar",
    pathExists: existsIn([])
  });
  // Offering tasks that would fail the moment they run is worse than
  // offering none.
  assert.deepStrictEqual(specs, []);
});

test("two folders inside one project contribute one set of tasks", () => {
  const specs = createTaskSpecs({
    workspaceFolders: ["/work/project/src", "/work/project/tests"],
    executable: "cinnabar",
    pathExists: existsIn(["/work/project/build.cnb"])
  });
  assert.strictEqual(specs.length, TASK_TEMPLATES.length);
});

test("separate projects each contribute their own tasks", () => {
  const specs = createTaskSpecs({
    workspaceFolders: ["/work/one", "/work/two"],
    executable: "cinnabar",
    pathExists: existsIn(["/work/one/build.cnb", "/work/two/build.cnb"])
  });
  assert.strictEqual(specs.length, TASK_TEMPLATES.length * 2);
});

test("the configured executable is the one the task runs", () => {
  const specs = createTaskSpecs({
    workspaceFolders: ["/work/project"],
    executable: "/opt/cinnabar/bin/cinnabar",
    pathExists: existsIn(["/work/project/build.cnb"])
  });
  assert.ok(specs.every((spec) => spec.command === "/opt/cinnabar/bin/cinnabar"));
  assert.ok(specs.every((spec) => spec.commandLine.startsWith("/opt/cinnabar/bin/cinnabar ")));
});

test("only arguments with whitespace are quoted", () => {
  assert.strictEqual(quoteCommandLine("cinnabar", ["build", "/work/project"]), "cinnabar build /work/project");
  assert.strictEqual(
    quoteCommandLine("cinnabar", ["build", "/work/my project"]),
    'cinnabar build "/work/my project"'
  );
});

test("no template declares a problem matcher", () => {
  // The language server already publishes the compiler's diagnostics with
  // real spans. A matcher scraping the same errors out of terminal text
  // would double every one of them in the Problems panel.
  for (const template of TASK_TEMPLATES) {
    assert.ok(!Object.prototype.hasOwnProperty.call(template, "problemMatcher"));
  }
});
