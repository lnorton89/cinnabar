// The tabs: one per compiler document, each showing what it contains.
//
// Every number and name below is read straight out of the response. None of
// these views computes a fact about the program — a size, an offset, a
// position — because the compiler already did, and a second computation
// here could disagree with the binary a real build produces.

const NOTHING_YET = "Compile something to see this.";

function Empty({ children }) {
  return <p className="empty">{children}</p>;
}

/** A section the server reported as unavailable, with the reason it gave. */
function SectionFailure({ section }) {
  return (
    <div className="failure">
      <p>The compiler did not produce this document.</p>
      <pre>{section.error}</pre>
    </div>
  );
}

function spanLabel(source) {
  if (!source) {
    return null;
  }
  if (typeof source.start_line !== "number") {
    return `bytes ${source.start}–${source.end}`;
  }
  return `line ${source.start_line + 1}, column ${source.start_column + 1}`;
}

/**
 * A diagnostic, with the explanations the checker attached to it.
 *
 * The explanation's `kind` is what decides its colour, never its wording:
 * the message is prose the compiler may reword, the kind is the vocabulary
 * it classifies by.
 */
export function DiagnosticsView({ result, onReveal }) {
  if (!result) {
    return <Empty>{NOTHING_YET}</Empty>;
  }
  if (!result.diagnostics.ok) {
    return <SectionFailure section={result.diagnostics} />;
  }
  const diagnostics = result.diagnostics.document.diagnostics;
  if (diagnostics.length === 0) {
    return <Empty>No diagnostics. The front end resolved, typed, and borrow-checked this program.</Empty>;
  }
  return (
    <ul className="diagnostics">
      {diagnostics.map((diagnostic, index) => (
        <li key={index} className="diagnostic">
          <button type="button" className="diagnostic__head" onClick={() => onReveal(diagnostic.source)}>
            <span className="diagnostic__severity">{diagnostic.severity}</span>
            <span className="diagnostic__message">{diagnostic.message}</span>
            {diagnostic.source ? <span className="diagnostic__where">{spanLabel(diagnostic.source)}</span> : null}
          </button>
          {diagnostic.explanations.length > 0 ? (
            <ul className="explanations">
              {diagnostic.explanations.map((explanation, position) => (
                <li key={position} className={`explanation explanation--${explanation.kind}`}>
                  <button type="button" onClick={() => onReveal(explanation.source)}>
                    <span className="explanation__kind">{explanation.kind}</span>
                    <span>{explanation.message}</span>
                    {explanation.source ? (
                      <span className="explanation__where">{spanLabel(explanation.source)}</span>
                    ) : null}
                  </button>
                </li>
              ))}
            </ul>
          ) : null}
        </li>
      ))}
    </ul>
  );
}

/**
 * The node arena.
 *
 * Rendered as rows rather than as pretty-printed JSON: the arena is a table
 * — one row per node, with its tag, its span, its slots, and whatever the
 * pipeline attached to it — and a table is what it reads as.
 */
export function AstView({ section, title }) {
  if (!section) {
    return <Empty>{NOTHING_YET}</Empty>;
  }
  if (!section.ok) {
    return <SectionFailure section={section} />;
  }
  const { nodes, names, lists, root, format } = section.document;
  return (
    <div className="arena">
      <p className="arena__caption">
        <code>{format}</code> — {title}. {nodes.length} nodes, {names.length} interned names, {lists.length} lists;
        the root item list is <code>#{root}</code>.
      </p>
      <div className="table-scroll">
        <table className="nodes">
          <thead>
            <tr>
              <th>id</th>
              <th>tag</th>
              <th>where</th>
              <th>detail</th>
            </tr>
          </thead>
          <tbody>
            {nodes.map((node) => (
              <tr key={node.id}>
                <td className="num">{node.id}</td>
                <td>{node.tag}</td>
                <td className="num">{node.source ? spanLabel(node.source) : "—"}</td>
                <td>{node.detail ? <DetailCell detail={node.detail} /> : "—"}</td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>
    </div>
  );
}

function DetailCell({ detail }) {
  const { kind, subkind, ...facts } = detail;
  return (
    <span className="detail">
      <span className="detail__kind">
        {kind}
        {subkind ? ` ${subkind}` : ""}
      </span>
      {Object.entries(facts).map(([name, value]) => (
        <span key={name} className="detail__fact">
          <span className="detail__name">{name}</span>
          <span className="detail__value">
            {value && typeof value === "object" ? `${value.key} ${value.rendered}` : String(value)}
          </span>
        </span>
      ))}
    </span>
  );
}

/** Sizes, alignments, field offsets, and variant tags, as measured. */
export function LayoutView({ section }) {
  if (!section) {
    return <Empty>{NOTHING_YET}</Empty>;
  }
  if (!section.ok) {
    return <SectionFailure section={section} />;
  }
  const { types, target } = section.document;
  if (types.length === 0) {
    return <Empty>This program declares no concrete struct, enum, or native handle.</Empty>;
  }
  return (
    <div className="layout">
      <p className="arena__caption">
        Measured for <code>{target}</code> through the same lowering a real build uses.
      </p>
      {types.map((entry) => (
        <div key={entry.key} className="layout__type">
          <h3>
            <span className="layout__kind">{entry.kind}</span> {entry.type}
            <span className="layout__size">
              size {entry.size}, align {entry.align}
              {entry.kind === "enum" ? `, tag ${entry.tag_type}` : ""}
              {entry.kind === "enum" && entry.payload_offset !== null
                ? `, payload at ${entry.payload_offset}`
                : ""}
            </span>
          </h3>
          {entry.fields ? (
            <table className="layout__members">
              <thead>
                <tr>
                  <th>field</th>
                  <th>type</th>
                  <th>offset</th>
                  <th>size</th>
                </tr>
              </thead>
              <tbody>
                {entry.fields.map((field) => (
                  <tr key={field.name}>
                    <td>{field.name}</td>
                    <td>{field.type}</td>
                    <td className="num">{field.offset}</td>
                    <td className="num">{field.size}</td>
                  </tr>
                ))}
              </tbody>
            </table>
          ) : null}
          {entry.variants ? (
            <table className="layout__members">
              <thead>
                <tr>
                  <th>variant</th>
                  <th>tag</th>
                  <th>payload size</th>
                </tr>
              </thead>
              <tbody>
                {entry.variants.map((variant) => (
                  <tr key={variant.name}>
                    <td>{variant.name}</td>
                    <td className="num">{variant.tag}</td>
                    <td className="num">{variant.payload_size}</td>
                  </tr>
                ))}
              </tbody>
            </table>
          ) : null}
          {entry.opaque ? <p className="layout__opaque">An opaque handle: user code never sees inside it.</p> : null}
        </div>
      ))}
    </div>
  );
}

/** The IR as emitted, before optimization. */
export function IrView({ section }) {
  if (!section) {
    return <Empty>{NOTHING_YET}</Empty>;
  }
  if (!section.ok) {
    return <SectionFailure section={section} />;
  }
  return <pre className="ir">{section.text}</pre>;
}

/** What the program did: its streams and the status it exited with. */
export function ProgramView({ result }) {
  if (!result) {
    return <Empty>{NOTHING_YET}</Empty>;
  }
  if (!result.accepted) {
    return <Empty>This program was rejected, so there was nothing to run.</Empty>;
  }
  if (!result.program) {
    return <Empty>Press Run to execute this program.</Empty>;
  }
  if (!result.program.ok) {
    return (
      <div className="failure">
        <p>The program did not finish.</p>
        <pre>{result.program.error}</pre>
      </div>
    );
  }
  const { exitCode, stdout, stderr, truncated } = result.program;
  return (
    <div className="program">
      <p className={exitCode === 0 ? "exit exit--ok" : "exit exit--nonzero"}>Exited with status {exitCode}</p>
      {stdout ? (
        <>
          <h3>stdout</h3>
          <pre>{stdout}</pre>
        </>
      ) : null}
      {stderr ? (
        <>
          <h3>stderr</h3>
          <pre>{stderr}</pre>
        </>
      ) : null}
      {!stdout && !stderr ? <Empty>The program wrote nothing.</Empty> : null}
      {truncated ? <p className="note">Output was truncated at the service&rsquo;s limit.</p> : null}
    </div>
  );
}
