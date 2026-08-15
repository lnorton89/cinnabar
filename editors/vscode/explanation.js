// Renders a borrow explanation as a control-flow diagram for the webview.
//
// The compiler already knows why it rejected a program: which span bound a
// linear value, which branches consumed it, which branches left it live,
// where it was already moved. In a terminal that arrives as a stack of
// labels the reader has to reassemble into a shape. The shape is the whole
// point, so this module draws it: a binding at the top, the branches that
// disagree as parallel lanes below it, and the guidance last.
//
// Every node is classified by the `kind` the borrow checker attached, never
// by matching the wording of its message. The messages are prose and may be
// reworded; the kinds are the checker's own vocabulary.

const KIND_ORDER = ["binding", "moved", "consumed", "live", "context", "guidance"];

const KIND_PRESENTATION = {
  binding: { label: "bound here", tone: "bind", lane: "trunk" },
  moved: { label: "already moved", tone: "move", lane: "trunk" },
  consumed: { label: "consumed on this path", tone: "consume", lane: "branch" },
  live: { label: "still live on this path", tone: "leak", lane: "branch" },
  context: { label: "context", tone: "context", lane: "trunk" },
  guidance: { label: "what to do", tone: "guide", lane: "trunk" }
};

function presentationOf(kind) {
  return KIND_PRESENTATION[kind] || KIND_PRESENTATION.context;
}

function escapeHtml(text) {
  return String(text === undefined || text === null ? "" : text)
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;");
}

/** `path/to/file.cnb:12` for a location, or an empty string when it has none. */
function describeLocation(location) {
  if (!location || typeof location.uri !== "string") {
    return "";
  }
  const segments = location.uri.split("/");
  const name = decodeURIComponent(segments[segments.length - 1] || location.uri);
  const line = location.range && location.range.start ? location.range.start.line : undefined;
  return typeof line === "number" ? `${name}:${line + 1}` : name;
}

/**
 * Group the explanations into the lanes the diagram draws.
 *
 * `consumed` and `live` notes are what a linear-value join failure is made
 * of — the same value, two paths, two different answers — so they are the
 * only ones drawn side by side. Everything else is a single column, in the
 * order the checker raised it within its kind.
 */
function layoutExplanations(explanations) {
  const list = Array.isArray(explanations) ? explanations : [];
  const indexed = list.map((explanation, index) => ({ ...explanation, index }));
  const trunkBefore = [];
  const branches = [];
  const trunkAfter = [];
  for (const explanation of indexed) {
    const presentation = presentationOf(explanation.kind);
    if (presentation.lane === "branch") {
      branches.push(explanation);
    } else if (explanation.kind === "guidance") {
      trunkAfter.push(explanation);
    } else {
      trunkBefore.push(explanation);
    }
  }
  const rank = (explanation) => {
    const position = KIND_ORDER.indexOf(explanation.kind);
    return position === -1 ? KIND_ORDER.length : position;
  };
  trunkBefore.sort((left, right) => rank(left) - rank(right) || left.index - right.index);
  return { trunkBefore, branches, trunkAfter };
}

function renderNode(explanation, focus) {
  const presentation = presentationOf(explanation.kind);
  const place = describeLocation(explanation.location);
  const focused = explanation.index === focus ? " node--focus" : "";
  const jumpable = explanation.location ? "" : " node--placeless";
  return `<button class="node node--${presentation.tone}${focused}${jumpable}" data-index="${explanation.index}"${
    explanation.location ? "" : " disabled"
  }>
      <span class="node__kind">${escapeHtml(presentation.label)}</span>
      <span class="node__message">${escapeHtml(explanation.message)}</span>
      ${place ? `<span class="node__place">${escapeHtml(place)}</span>` : ""}
    </button>`;
}

function renderBranches(branches, focus) {
  if (branches.length === 0) {
    return "";
  }
  // One lane per branch, with a fork above and a join below: that is the
  // literal shape of the disagreement the checker found, and the reason the
  // program is rejected is that the lanes do not agree at the join.
  const lanes = branches.map((explanation) => `<div class="lane">${renderNode(explanation, focus)}</div>`).join("");
  return `<div class="fork" aria-hidden="true"></div>
    <div class="lanes" style="--lane-count: ${branches.length}">${lanes}</div>
    <div class="join" aria-hidden="true"></div>
    <p class="verdict">The paths disagree here, so the value's fate is not the same on every route out.</p>`;
}

/**
 * The full webview document for one explanation.
 *
 * `nonce` is the content-security-policy nonce the host generated for this
 * panel; the page loads nothing from anywhere, so the only script that runs
 * is the one carrying it.
 */
function renderExplanationHtml(explanation, nonce) {
  const payload = explanation && typeof explanation === "object" ? explanation : {};
  const diagnostic = payload.diagnostic || {};
  const focus = typeof payload.focus === "number" ? payload.focus : -1;
  const { trunkBefore, branches, trunkAfter } = layoutExplanations(payload.explanations);
  const diagnosticPlace = describeLocation(diagnostic.location);
  const hasBody = trunkBefore.length + branches.length + trunkAfter.length > 0;
  const body = hasBody
    ? `${trunkBefore.map((explanation) => renderNode(explanation, focus)).join("")}
       ${renderBranches(branches, focus)}
       ${trunkAfter.map((explanation) => renderNode(explanation, focus)).join("")}`
    : `<p class="empty">The compiler attached no explanation to this diagnostic.</p>`;

  return `<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta http-equiv="Content-Security-Policy" content="default-src 'none'; style-src 'unsafe-inline'; script-src 'nonce-${nonce}';">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Cinnabar borrow explanation</title>
<style>
  :root { color-scheme: light dark; }
  body {
    margin: 0;
    padding: 20px 22px 32px;
    font-family: var(--vscode-font-family);
    font-size: var(--vscode-font-size);
    color: var(--vscode-foreground);
    background: var(--vscode-editor-background);
  }
  h1 {
    margin: 0 0 4px;
    font-size: 1.05rem;
    font-weight: 600;
    color: var(--vscode-editorError-foreground, var(--vscode-errorForeground, #d33));
  }
  .where { margin: 0 0 20px; opacity: 0.75; font-family: var(--vscode-editor-font-family); font-size: 0.85em; }
  .flow { display: flex; flex-direction: column; align-items: stretch; gap: 0; }
  .node {
    display: block;
    width: 100%;
    text-align: left;
    padding: 10px 12px;
    border: 1px solid var(--vscode-panel-border, rgba(128,128,128,0.35));
    border-left-width: 3px;
    border-radius: 4px;
    background: var(--vscode-editorWidget-background, transparent);
    color: inherit;
    font: inherit;
    cursor: pointer;
  }
  .node:hover:not(:disabled) { background: var(--vscode-list-hoverBackground, rgba(128,128,128,0.12)); }
  .node:disabled { cursor: default; opacity: 0.7; }
  .node--focus { outline: 1px solid var(--vscode-focusBorder); outline-offset: 1px; }
  .node + .node { margin-top: 14px; }
  .node__kind {
    display: block;
    font-size: 0.72em;
    letter-spacing: 0.08em;
    text-transform: uppercase;
    opacity: 0.8;
    margin-bottom: 4px;
  }
  .node__message { display: block; line-height: 1.45; }
  .node__place {
    display: block;
    margin-top: 6px;
    font-family: var(--vscode-editor-font-family);
    font-size: 0.8em;
    opacity: 0.65;
  }
  .node--bind { border-left-color: var(--vscode-charts-blue, #3794ff); }
  .node--move { border-left-color: var(--vscode-charts-purple, #b180d7); }
  .node--consume { border-left-color: var(--vscode-charts-green, #89d185); }
  .node--leak { border-left-color: var(--vscode-charts-red, #f14c4c); }
  .node--guide { border-left-color: var(--vscode-charts-yellow, #cca700); }
  .node--context { border-left-color: var(--vscode-panel-border, rgba(128,128,128,0.5)); }
  .fork, .join {
    align-self: center;
    width: 1px;
    height: 18px;
    background: var(--vscode-panel-border, rgba(128,128,128,0.5));
  }
  .lanes {
    display: grid;
    grid-template-columns: repeat(var(--lane-count), minmax(0, 1fr));
    gap: 12px;
    position: relative;
    padding-top: 12px;
  }
  .lanes::before {
    content: "";
    position: absolute;
    top: 0;
    left: calc(50% / var(--lane-count));
    right: calc(50% / var(--lane-count));
    height: 1px;
    background: var(--vscode-panel-border, rgba(128,128,128,0.5));
  }
  .lane { display: flex; }
  .lane .node { align-self: stretch; }
  .verdict { margin: 12px 0 0; opacity: 0.8; line-height: 1.5; }
  .empty { opacity: 0.75; }
</style>
</head>
<body>
  <h1>${escapeHtml(diagnostic.message || "Borrow explanation")}</h1>
  ${diagnosticPlace ? `<p class="where">${escapeHtml(diagnosticPlace)}</p>` : ""}
  <div class="flow">${body}</div>
<script nonce="${nonce}">
  const vscode = acquireVsCodeApi();
  for (const node of document.querySelectorAll(".node[data-index]")) {
    node.addEventListener("click", () => {
      vscode.postMessage({ type: "reveal", index: Number(node.dataset.index) });
    });
  }
</script>
</body>
</html>`;
}

module.exports = {
  renderExplanationHtml,
  layoutExplanations,
  describeLocation
};
