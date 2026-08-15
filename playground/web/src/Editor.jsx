// The Monaco editor, with the compiler's diagnostics drawn onto it.
//
// Markers come from the `--emit-json` diagnostic envelope, which carries
// both byte offsets and the line/UTF-16-column pair Monaco wants — mapped
// by the compiler through the same function the language server uses. So a
// squiggle here is in the same place the editor extension would put it, and
// neither had to compute a position from the other's.

import { forwardRef, useEffect, useImperativeHandle, useRef } from "react";
// The editor core only. The default entry point pulls every language
// Monaco ships with — TypeScript, JSON, HTML, and forty others — none of
// which this page can open. Importing the API directly leaves a bundle
// holding one language: Cinnabar.
import * as monaco from "monaco-editor/esm/vs/editor/editor.api";
import { registerCinnabar } from "cinnabar-monaco";

const languageId = registerCinnabar(monaco);

const Editor = forwardRef(function Editor({ value, onChange, diagnostics }, ref) {
  const host = useRef(null);
  const editor = useRef(null);

  useEffect(() => {
    if (!host.current || editor.current) {
      return undefined;
    }
    editor.current = monaco.editor.create(host.current, {
      value,
      language: languageId,
      automaticLayout: true,
      minimap: { enabled: false },
      fontLigatures: false,
      scrollBeyondLastLine: false,
      renderWhitespace: "none",
      tabSize: 2,
      theme: window.matchMedia?.("(prefers-color-scheme: dark)").matches ? "vs-dark" : "vs",
    });
    const subscription = editor.current.onDidChangeModelContent(() => {
      onChange(editor.current.getValue());
    });
    return () => {
      subscription.dispose();
      editor.current?.dispose();
      editor.current = null;
    };
    // Created once. `value` is applied below when it changes from outside,
    // which is what choosing an example does; re-creating the editor for
    // every keystroke would lose the cursor.
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, []);

  useEffect(() => {
    const instance = editor.current;
    if (instance && instance.getValue() !== value) {
      instance.setValue(value);
    }
  }, [value]);

  useEffect(() => {
    const instance = editor.current;
    if (!instance) {
      return;
    }
    const model = instance.getModel();
    if (!model) {
      return;
    }
    const markers = [];
    for (const diagnostic of diagnostics) {
      if (!diagnostic.source || typeof diagnostic.source.start_line !== "number") {
        // Diagnostics with a null source carry no line or column and are
        // skipped here; the Diagnostics tab still lists them.
        continue;
      }
      markers.push({
        severity: monaco.MarkerSeverity.Error,
        message: diagnostic.message,
        startLineNumber: diagnostic.source.start_line + 1,
        startColumn: diagnostic.source.start_column + 1,
        endLineNumber: diagnostic.source.end_line + 1,
        endColumn: diagnostic.source.end_column + 1,
        relatedInformation: diagnostic.explanations
          .filter((explanation) => explanation.source)
          .map((explanation) => ({
            message: `${explanation.kind}: ${explanation.message}`,
            resource: model.uri,
            startLineNumber: explanation.source.start_line + 1,
            startColumn: explanation.source.start_column + 1,
            endLineNumber: explanation.source.end_line + 1,
            endColumn: explanation.source.end_column + 1,
          })),
      });
    }
    monaco.editor.setModelMarkers(model, "cinnabar", markers);
  }, [diagnostics]);

  useImperativeHandle(ref, () => ({
    revealSpan(span) {
      const instance = editor.current;
      if (!instance || !span || typeof span.start_line !== "number") {
        return;
      }
      const selection = {
        startLineNumber: span.start_line + 1,
        startColumn: span.start_column + 1,
        endLineNumber: span.end_line + 1,
        endColumn: span.end_column + 1,
      };
      instance.setSelection(selection);
      instance.revealRangeInCenter(selection);
      instance.focus();
    },
  }));

  return <div className="editor" ref={host} />;
});

export default Editor;
