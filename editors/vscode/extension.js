const fs = require("node:fs");
const vscode = require("vscode");
const languageClient = require("vscode-languageclient/node");
const { createLaunchPlan } = require("./lsp-launcher");
const { createTaskSpecs } = require("./tasks");
const { renderExplanationHtml } = require("./explanation");

const TASK_TYPE = "cinnabar";

let client;
let statusBarItem;
let explanationPanel;
// The explanations the open panel is currently showing. The panel is reused
// across code lenses, so its message handler is registered once at creation
// and reads this; registering a fresh handler per explanation would leave
// the previous ones attached and reveal a stale span on every click after
// the first.
let explanationNodes = [];

// vscode-languageclient's State enum (Stopped = 1, Starting = 3, Running = 5)
// isn't re-exported through a require() we can destructure cleanly here, so
// the status bar renders straight off the numeric State it hands
// onDidChangeState rather than importing the enum for three labels.
const STATE_PRESENTATION = {
  [languageClient.State.Stopped]: { text: "$(circle-slash) Cinnabar", tooltip: "Cinnabar Language Server is stopped" },
  [languageClient.State.Starting]: { text: "$(sync~spin) Cinnabar", tooltip: "Cinnabar Language Server is starting…" },
  [languageClient.State.Running]: { text: "$(check) Cinnabar", tooltip: "Cinnabar Language Server is running" }
};

function renderState(state) {
  if (!statusBarItem) {
    return;
  }
  const presentation = STATE_PRESENTATION[state] || STATE_PRESENTATION[languageClient.State.Stopped];
  statusBarItem.text = presentation.text;
  statusBarItem.tooltip = presentation.tooltip;
}

function startClient() {
  const configuration = vscode.workspace.getConfiguration("cinnabar");
  const workspaceFolders = (vscode.workspace.workspaceFolders || []).map(
    (workspaceFolder) => workspaceFolder.uri.fsPath
  );
  let launchPlan;
  try {
    launchPlan = createLaunchPlan({
      mode: configuration.get("server.mode", "auto"),
      serverPath: configuration.get("server.path", ""),
      workspaceFolders
    });
  } catch (error) {
    vscode.window.showErrorMessage(`Unable to start Cinnabar Language Server: ${error.message}`);
    return;
  }
  const serverOptions = {
    ...launchPlan,
    transport: languageClient.TransportKind.stdio
  };
  const clientOptions = {
    documentSelector: [
      {
        scheme: "file",
        language: "cinnabar"
      }
    ],
    synchronize: {
      fileEvents: vscode.workspace.createFileSystemWatcher("**/*.cnb")
    }
  };
  client = new languageClient.LanguageClient(
    "cinnabar",
    "Cinnabar Language Server",
    serverOptions,
    clientOptions
  );
  client.onDidChangeState((event) => renderState(event.newState));
  renderState(languageClient.State.Starting);
  // `client.start()` returns a Promise<void> under vscode-languageclient ^9,
  // not a Disposable -- pushing it into context.subscriptions makes VS Code
  // call .dispose() on a Promise when the extension deactivates, which
  // throws. deactivate() below already stops the client, so start() needs
  // nothing pushed; it only needs its rejection surfaced instead of left
  // unhandled.
  client.start().catch((error) => {
    vscode.window.showErrorMessage(`Cinnabar Language Server failed to start: ${error.message}`);
  });
}

async function restartServer() {
  if (!client) {
    startClient();
    return;
  }
  try {
    await client.stop();
  } catch (error) {
    // Falls through to starting a fresh client regardless of how the old
    // one shut down -- a client wedged mid-stop is exactly what "restart"
    // needs to recover from.
  }
  startClient();
}

function showOutputChannel() {
  if (!client) {
    vscode.window.showInformationMessage("Cinnabar Language Server has not started yet.");
    return;
  }
  client.outputChannel.show();
}

// One panel, reused. A borrow explanation is something you read while
// editing the code it is about, and a new tab per code lens would bury the
// editor the reader is trying to get back to.
function showExplanation(explanation) {
  if (typeof explanation === "string") {
    // A checkout whose language server predates structured explanations
    // still sends the bare sentence. Showing it is better than showing
    // nothing, and it costs one branch.
    vscode.window.showInformationMessage(explanation);
    return;
  }
  if (!explanation || typeof explanation !== "object") {
    return;
  }
  if (!explanationPanel) {
    explanationPanel = vscode.window.createWebviewPanel(
      "cinnabar.explanation",
      "Cinnabar: Borrow Explanation",
      { viewColumn: vscode.ViewColumn.Beside, preserveFocus: true },
      { enableScripts: true, retainContextWhenHidden: true }
    );
    explanationPanel.webview.onDidReceiveMessage((message) => {
      if (!message || message.type !== "reveal") {
        return;
      }
      const target = explanationNodes[message.index];
      if (!target || !target.location) {
        return;
      }
      revealLocation(target.location);
    });
    explanationPanel.onDidDispose(() => {
      explanationPanel = undefined;
      explanationNodes = [];
    });
  }
  explanationNodes = Array.isArray(explanation.explanations) ? explanation.explanations : [];
  const nonce = createNonce();
  explanationPanel.webview.html = renderExplanationHtml(explanation, nonce);
  explanationPanel.reveal(vscode.ViewColumn.Beside, true);
}

function revealLocation(location) {
  const range = location.range || {};
  const start = range.start || { line: 0, character: 0 };
  const end = range.end || start;
  const selection = new vscode.Range(start.line, start.character, end.line, end.character);
  vscode.window.showTextDocument(vscode.Uri.parse(location.uri), {
    selection,
    viewColumn: vscode.ViewColumn.One
  });
}

function createNonce() {
  const alphabet = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789";
  let nonce = "";
  for (let index = 0; index < 32; index += 1) {
    nonce += alphabet.charAt(Math.floor(Math.random() * alphabet.length));
  }
  return nonce;
}

// Tasks are resolved fresh on every request rather than cached: a manifest
// can appear in a folder while the window is open, and a picker that still
// showed yesterday's project list would be wrong in exactly the case a new
// contributor hits first.
function provideTasks() {
  const configuration = vscode.workspace.getConfiguration("cinnabar");
  const specs = createTaskSpecs({
    workspaceFolders: (vscode.workspace.workspaceFolders || []).map((folder) => folder.uri.fsPath),
    executable: configuration.get("compiler.path", "cinnabar"),
    pathExists: fs.existsSync
  });
  return specs.map((spec) => {
    const task = new vscode.Task(
      { type: TASK_TYPE, command: spec.name },
      vscode.TaskScope.Workspace,
      spec.name,
      "cinnabar",
      new vscode.ShellExecution(spec.commandLine, { cwd: spec.cwd })
    );
    task.detail = spec.detail;
    return task;
  });
}

function activate(context) {
  statusBarItem = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Right, 0);
  statusBarItem.command = "cinnabar.showOutputChannel";
  renderState(languageClient.State.Stopped);
  statusBarItem.show();
  context.subscriptions.push(statusBarItem);

  context.subscriptions.push(
    vscode.commands.registerCommand("cinnabar.showExplanation", showExplanation),
    vscode.commands.registerCommand("cinnabar.restartServer", restartServer),
    vscode.commands.registerCommand("cinnabar.showOutputChannel", showOutputChannel),
    vscode.tasks.registerTaskProvider(TASK_TYPE, {
      provideTasks,
      // Every task this provider offers is fully resolved when it is
      // offered, so a task read back from tasks.json needs nothing filled
      // in and is returned unchanged.
      resolveTask: (task) => task
    })
  );

  startClient();
}

function deactivate() {
  if (!client) {
    return undefined;
  }
  return client.stop();
}

module.exports = {
  activate,
  deactivate
};
