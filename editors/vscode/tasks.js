// The Cinnabar task definitions the extension contributes.
//
// `cinnabar build`, `run`, `check`, and `test` are the whole project
// surface, and each one already discovers its own manifest by walking
// upward from the path it is given. So a task is nothing more than a
// command line plus the directory to run it in, and this module builds
// those without importing `vscode` — which is what lets the selection rules
// be tested without an editor.

const path = require("node:path");

const MANIFEST_FILE = "build.cnb";

// Every task the extension offers, in the order a picker shows them. The
// `problem matcher` is deliberately absent: the language server already
// publishes the compiler's diagnostics with real spans, and a second set
// scraped out of terminal text would double every error in the Problems
// panel and disagree with the first the moment a message is reworded.
const TASK_TEMPLATES = [
  { name: "build", args: ["build"], detail: "Compile the project's entry source to target/<NAME>" },
  { name: "run", args: ["run"], detail: "Build the project, then execute the artifact" },
  { name: "check", args: ["check"], detail: "Run the front end only — no codegen, no link" },
  { name: "test", args: ["test"], detail: "Compile and run every .cnb file under the manifest's TESTS directory" },
  {
    name: "test (update snapshots)",
    args: ["test", "--update-snapshots"],
    detail: "Rewrite .stderr diagnostic snapshots from what the compiler now prints"
  }
];

function isNonEmptyString(value) {
  return typeof value === "string" && value.trim().length > 0;
}

/**
 * The nearest ancestor of `startPath` that holds a `build.cnb`, or
 * undefined.
 *
 * A Cinnabar project is defined by its manifest, not by the folder someone
 * opened, so a workspace whose sources live in a subdirectory still gets
 * its tasks — and a folder with no manifest anywhere above it gets none,
 * rather than tasks that would fail on invocation.
 */
function findProjectRoot(startPath, pathExists) {
  if (!isNonEmptyString(startPath) || typeof pathExists !== "function") {
    return undefined;
  }
  let candidate = path.resolve(startPath);
  while (true) {
    if (pathExists(path.join(candidate, MANIFEST_FILE))) {
      return candidate;
    }
    const parent = path.dirname(candidate);
    if (parent === candidate) {
      return undefined;
    }
    candidate = parent;
  }
}

/**
 * One task specification per template per project found under the given
 * workspace folders.
 *
 * Two workspace folders inside one project would otherwise contribute the
 * same task twice, so roots are deduplicated: the task list describes
 * projects, not folders.
 */
function createTaskSpecs({ workspaceFolders, executable, pathExists }) {
  const folders = Array.isArray(workspaceFolders) ? workspaceFolders : [];
  const command = isNonEmptyString(executable) ? executable : "cinnabar";
  const roots = [];
  for (const folder of folders) {
    const root = findProjectRoot(folder, pathExists);
    if (root !== undefined && !roots.includes(root)) {
      roots.push(root);
    }
  }
  const specs = [];
  for (const root of roots) {
    for (const template of TASK_TEMPLATES) {
      specs.push({
        name: template.name,
        detail: template.detail,
        cwd: root,
        command,
        // Every project command takes the path it should act on. Passing the
        // root explicitly means the task does not depend on where the
        // terminal happened to start.
        args: [...template.args, root],
        commandLine: quoteCommandLine(command, [...template.args, root])
      });
    }
  }
  return specs;
}

/**
 * A shell command line for `command` and `args`.
 *
 * Only arguments containing whitespace are quoted, so the common case reads
 * exactly as a person would have typed it into the terminal the task opens.
 */
function quoteCommandLine(command, args) {
  const quote = (value) => (/\s/.test(value) ? `"${value.replace(/"/g, '\\"')}"` : value);
  return [command, ...args].map(quote).join(" ");
}

module.exports = {
  MANIFEST_FILE,
  TASK_TEMPLATES,
  findProjectRoot,
  createTaskSpecs,
  quoteCommandLine
};
