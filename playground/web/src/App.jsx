// The playground: an editor on the left, what the compiler said on the right.
//
// The tabs are the compiler's own surfaces, one per `--emit-json` document,
// and each one shows what that document actually contains rather than a
// summary of it. That is the whole point of the service: a reader who wants
// to know what the compiler thinks of their program should be able to see
// it, not be told about it.
//
// Nothing here re-derives anything. A diagnostic's position, a type's size,
// a variant's tag — all of it is read out of the response.

import { useCallback, useEffect, useMemo, useRef, useState } from "react";
import Editor from "./Editor.jsx";
import { DiagnosticsView, AstView, LayoutView, IrView, ProgramView } from "./views.jsx";

const TABS = [
  { id: "diagnostics", label: "Diagnostics" },
  { id: "program", label: "Program" },
  { id: "ast", label: "AST" },
  { id: "typed", label: "Typed AST" },
  { id: "layout", label: "Layout" },
  { id: "ir", label: "LLVM IR" },
];

const FALLBACK_SOURCE = `pub fun main() I64
  return 0
end
`;

export default function App() {
  const [examples, setExamples] = useState([]);
  const [exampleId, setExampleId] = useState(null);
  const [source, setSource] = useState(FALLBACK_SOURCE);
  const [result, setResult] = useState(null);
  const [pending, setPending] = useState(false);
  const [failure, setFailure] = useState(null);
  const [tab, setTab] = useState("diagnostics");
  const editorRef = useRef(null);

  useEffect(() => {
    let cancelled = false;
    fetch("/api/examples")
      .then((response) => response.json())
      .then((body) => {
        if (cancelled || !Array.isArray(body.examples) || body.examples.length === 0) {
          return;
        }
        setExamples(body.examples);
        setExampleId(body.examples[0].id);
        setSource(body.examples[0].source);
      })
      .catch(() => {
        // A missing example corpus is not worth an error banner: the editor
        // still works, it just opens on the fallback program.
      });
    return () => {
      cancelled = true;
    };
  }, []);

  const submit = useCallback(
    async (execute) => {
      setPending(true);
      setFailure(null);
      try {
        const response = await fetch("/api/compile", {
          method: "POST",
          headers: { "content-type": "application/json" },
          body: JSON.stringify({ source, execute }),
        });
        const body = await response.json();
        if (!response.ok) {
          setFailure(body.error || `the service answered ${response.status}`);
          setResult(null);
          return;
        }
        setResult(body);
        // Land the reader on the tab that has the answer they asked for: a
        // rejected program's answer is its diagnostics, and a run's answer
        // is what the program did.
        if (!body.accepted) {
          setTab("diagnostics");
        } else if (execute) {
          setTab("program");
        }
      } catch (error) {
        setFailure(error.message);
        setResult(null);
      } finally {
        setPending(false);
      }
    },
    [source],
  );

  // Ctrl/Cmd+Enter runs, which is the shortcut every editor-shaped thing
  // has and the one a visitor will try first.
  useEffect(() => {
    function onKeyDown(event) {
      if ((event.metaKey || event.ctrlKey) && event.key === "Enter") {
        event.preventDefault();
        submit(true);
      }
    }
    window.addEventListener("keydown", onKeyDown);
    return () => window.removeEventListener("keydown", onKeyDown);
  }, [submit]);

  const diagnostics = useMemo(() => {
    const document = result?.diagnostics?.ok ? result.diagnostics.document : null;
    return Array.isArray(document?.diagnostics) ? document.diagnostics : [];
  }, [result]);

  const verdict = useMemo(() => {
    if (pending) {
      return { tone: "pending", text: "Compiling…" };
    }
    if (failure) {
      return { tone: "error", text: failure };
    }
    if (!result) {
      return { tone: "idle", text: "Not compiled yet" };
    }
    if (result.accepted) {
      return { tone: "ok", text: "Accepted — the front end found nothing to object to" };
    }
    const count = diagnostics.length;
    return { tone: "error", text: `Rejected — ${count} diagnostic${count === 1 ? "" : "s"}` };
  }, [pending, failure, result, diagnostics]);

  function chooseExample(id) {
    const example = examples.find((entry) => entry.id === id);
    if (!example) {
      return;
    }
    setExampleId(id);
    setSource(example.source);
    setResult(null);
    setFailure(null);
  }

  function revealSpan(span) {
    if (!span || !editorRef.current) {
      return;
    }
    editorRef.current.revealSpan(span);
  }

  const selected = examples.find((entry) => entry.id === exampleId);

  return (
    <div className="app">
      <header className="masthead">
        <div className="masthead__titles">
          <h1>Cinnabar Playground</h1>
          <p>
            This compiles and runs your program on a server. Everything on the right is the compiler&rsquo;s own
            output — the same documents <code>cinnabar --emit-json</code> writes.
          </p>
        </div>
        <div className="masthead__actions">
          <label className="picker">
            <span>Example</span>
            <select value={exampleId ?? ""} onChange={(event) => chooseExample(event.target.value)}>
              {examples.map((example) => (
                <option key={example.id} value={example.id}>
                  {example.title}
                </option>
              ))}
            </select>
          </label>
          <button type="button" onClick={() => submit(false)} disabled={pending}>
            Check
          </button>
          <button type="button" className="primary" onClick={() => submit(true)} disabled={pending}>
            Run
          </button>
        </div>
      </header>

      {selected ? <p className="blurb">{selected.blurb}</p> : null}

      <main className="panes">
        <section className="pane pane--editor">
          <Editor ref={editorRef} value={source} onChange={setSource} diagnostics={diagnostics} />
        </section>

        <section className="pane pane--output">
          <div className={`verdict verdict--${verdict.tone}`}>{verdict.text}</div>
          <nav className="tabs">
            {TABS.map((entry) => (
              <button
                key={entry.id}
                type="button"
                className={entry.id === tab ? "tab tab--active" : "tab"}
                onClick={() => setTab(entry.id)}
              >
                {entry.label}
              </button>
            ))}
          </nav>
          <div className="tabbody">
            {tab === "diagnostics" ? <DiagnosticsView result={result} onReveal={revealSpan} /> : null}
            {tab === "program" ? <ProgramView result={result} /> : null}
            {tab === "ast" ? <AstView section={result?.ast} title="the arena as parsing left it" /> : null}
            {tab === "typed" ? (
              <AstView section={result?.typedAst} title="the same arena with every front-end attachment" />
            ) : null}
            {tab === "layout" ? <LayoutView section={result?.layout} /> : null}
            {tab === "ir" ? <IrView section={result?.llvmIr} /> : null}
          </div>
        </section>
      </main>
    </div>
  );
}
