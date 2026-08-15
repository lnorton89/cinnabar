import test from "node:test";
import assert from "node:assert";
import fs from "node:fs";
import path from "node:path";
import {
  KEYWORDS,
  CONTROL_KEYWORDS,
  MODIFIER_KEYWORDS,
  BUILTIN_TYPES,
  classifyIdentifier
} from "../src/language.js";
import { monarchLanguage, languageConfiguration, registerCinnabar, LANGUAGE_ID } from "../src/index.js";

const repoRoot = path.resolve(import.meta.dirname, "..", "..", "..");

// The compiler's own keyword table, read out of the source rather than
// copied. A keyword added to or removed from the language has to fail here,
// not sit in this package describing a language that moved on.
function compilerKeywords() {
  const source = fs.readFileSync(path.join(repoRoot, "src", "analysis.rs"), "utf8");
  const table = source.match(/const KEYWORDS: &\[&str\] = &\[([\s\S]*?)\];/);
  assert.ok(table, "could not find the KEYWORDS table in src/analysis.rs");
  return [...table[1].matchAll(/"([^"]+)"/g)].map((match) => match[1]);
}

test("the keyword list is the compiler's, in the compiler's order", () => {
  assert.deepStrictEqual(KEYWORDS, compilerKeywords());
});

test("control and modifier keywords are subsets, not second lists", () => {
  for (const keyword of CONTROL_KEYWORDS) {
    assert.ok(KEYWORDS.includes(keyword), `${keyword} is not a keyword`);
  }
  for (const keyword of MODIFIER_KEYWORDS) {
    // `mut` is the exception: it appears only inside `&mut`, never as a
    // standalone keyword, so the compiler's table does not list it.
    assert.ok(KEYWORDS.includes(keyword) || keyword === "mut", `${keyword} is not a keyword`);
  }
});

test("the tokenizer is built from those lists rather than its own copies", () => {
  assert.strictEqual(monarchLanguage.keywords, KEYWORDS);
  assert.strictEqual(monarchLanguage.controlKeywords, CONTROL_KEYWORDS);
  assert.strictEqual(monarchLanguage.builtinTypes, BUILTIN_TYPES);
});

test("casing alone classifies an identifier", () => {
  // This is the property that makes highlighting here semantic rather than
  // heuristic: the compiler rejects a mis-cased identifier, so shape is
  // enough.
  assert.strictEqual(classifyIdentifier("port_from_int"), "binding");
  assert.strictEqual(classifyIdentifier("MagicHeader"), "type");
  assert.strictEqual(classifyIdentifier("MAX_PORT"), "constant");
  assert.strictEqual(classifyIdentifier("Port"), "type");
  assert.strictEqual(classifyIdentifier("_leading"), "unknown");
});

test("SCREAMING_SNAKE_CASE is matched before PascalCase", () => {
  const rules = monarchLanguage.tokenizer.root.map((rule) => String(rule[0]));
  const constantRule = rules.findIndex((rule) => rule.includes("A-Z0-9_]+"));
  const typeRule = rules.findIndex((rule) => rule.includes("A-Za-z0-9]*/"));
  assert.ok(constantRule !== -1 && typeRule !== -1, "both identifier rules should be present");
  // `MAX_PORT` is a constant. Were PascalCase first it would claim `MAX`
  // and leave `_PORT` behind.
  assert.ok(constantRule < typeRule, "the constant rule must come first");
});

test("comments are matched before anything else", () => {
  // `#` always opens a comment in Cinnabar — there is no `#` operator and
  // no preprocessor — so nothing may claim one first.
  const first = String(monarchLanguage.tokenizer.root[0][0]);
  assert.ok(first.includes("#"), `expected a comment rule first, got ${first}`);
});

test("block comments do not nest, matching the compiler", () => {
  const blockRules = monarchLanguage.tokenizer.block.map((rule) => String(rule[0]));
  assert.ok(!blockRules.some((rule) => rule.includes("#\\|")), "a nesting rule would disagree with the lexer");
});

test("indentation follows `end` rather than braces", () => {
  const { increaseIndentPattern, decreaseIndentPattern } = languageConfiguration.indentationRules;
  assert.ok(increaseIndentPattern.test("pub fun main() I64"));
  assert.ok(increaseIndentPattern.test("  while count < 10"));
  assert.ok(decreaseIndentPattern.test("  end"));
  assert.ok(decreaseIndentPattern.test("  else"));
  assert.ok(!increaseIndentPattern.test("  return 0"));
});

test("registering wires the tokenizer and the configuration to one id", () => {
  const calls = [];
  const monaco = {
    languages: {
      register: (definition) => calls.push(["register", definition.id]),
      setLanguageConfiguration: (id) => calls.push(["configuration", id]),
      setMonarchTokensProvider: (id) => calls.push(["tokenizer", id])
    }
  };
  assert.strictEqual(registerCinnabar(monaco), LANGUAGE_ID);
  assert.deepStrictEqual(calls, [
    ["register", "cinnabar"],
    ["configuration", "cinnabar"],
    ["tokenizer", "cinnabar"]
  ]);
});
