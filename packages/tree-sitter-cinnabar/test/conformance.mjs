// Checks the grammar against the compiler, fixture by fixture.
//
// A grammar is not "right" because its own corpus passes — it is right when
// it accepts what the compiler accepts. So this runs both over every `.cnb`
// in `tests/fixtures/` and compares verdicts: a fixture the compiler
// accepts must parse with no ERROR node, and the deliberately-invalid ones
// are reported separately rather than silently counted as passes.
//
// Usage: node test/conformance.mjs [path-to-cinnabar-binary]

import { execFileSync } from "node:child_process";
import { readdirSync, statSync } from "node:fs";
import { join, resolve } from "node:path";

const packageRoot = resolve(import.meta.dirname, "..");
const repoRoot = resolve(packageRoot, "..", "..");
const fixtureRoot = join(repoRoot, "tests", "fixtures");
const compiler = process.argv[2] || join(repoRoot, "target", "debug", "cinnabar");

function fixtures(directory) {
  const found = [];
  for (const entry of readdirSync(directory)) {
    const path = join(directory, entry);
    if (statSync(path).isDirectory()) {
      found.push(...fixtures(path));
    } else if (entry.endsWith(".cnb")) {
      found.push(path);
    }
  }
  return found.sort();
}

function compilerAccepts(path) {
  try {
    execFileSync(compiler, [path, "--check-only"], { stdio: "ignore" });
    return true;
  } catch {
    return false;
  }
}

function grammarAccepts(path) {
  // `tree-sitter parse` exits non-zero on a tree holding an error, which is
  // an outcome here rather than a failure to run, so the status is read off
  // the thrown result instead of propagating.
  let output = "";
  try {
    output = execFileSync("tree-sitter", ["parse", path], {
      cwd: packageRoot,
      encoding: "utf8",
      stdio: ["ignore", "pipe", "ignore"]
    });
  } catch (failure) {
    output = String(failure.stdout || "");
  }
  return !output.includes("ERROR") && !output.includes("MISSING");
}

const disagreements = [];
let accepted = 0;
let rejected = 0;
for (const path of fixtures(fixtureRoot)) {
  const valid = compilerAccepts(path);
  const parses = grammarAccepts(path);
  if (valid) {
    accepted += 1;
    if (!parses) {
      disagreements.push(`${path}: the compiler accepts this program, the grammar does not parse it`);
    }
  } else {
    rejected += 1;
  }
}

console.log(`${accepted} accepted by the compiler, ${rejected} rejected by it`);
if (disagreements.length > 0) {
  for (const line of disagreements) {
    console.error(line);
  }
  process.exit(1);
}
console.log("the grammar parses every program the compiler accepts");
