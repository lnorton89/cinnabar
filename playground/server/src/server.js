// The playground's HTTP surface.
//
// Three endpoints and nothing else: a health check, the example corpus, and
// the compile-and-maybe-run call. It serves the built front end as static
// files when one has been built, so the whole thing is a single container
// rather than two.
//
// The interesting logic here is admission control, not routing. This
// service exists to run code strangers wrote, so it refuses more work than
// it can safely have in flight, refuses bodies larger than a submission
// could reasonably be, and refuses to keep reading a request that has
// already exceeded that. None of that is the sandbox — see
// `playground/README.md` — it is what keeps one visitor from being able to
// take the service away from the others.

import { createServer } from "node:http";
import { readFile, stat } from "node:fs/promises";
import { extname, join, normalize, resolve } from "node:path";
import { compileSubmission, MAX_SOURCE_BYTES } from "./compile.js";
import { EXAMPLES } from "./examples.js";

/** How many submissions may be compiling at once. */
export const MAX_CONCURRENT = 4;

/** Request bodies larger than this are refused without being read. */
const MAX_BODY_BYTES = MAX_SOURCE_BYTES + 1024;

const CONTENT_TYPES = {
  ".html": "text/html; charset=utf-8",
  ".js": "text/javascript; charset=utf-8",
  ".css": "text/css; charset=utf-8",
  ".json": "application/json; charset=utf-8",
  ".svg": "image/svg+xml",
  ".ico": "image/x-icon",
  ".woff2": "font/woff2",
  ".map": "application/json; charset=utf-8",
};

function sendJson(response, status, body) {
  const text = JSON.stringify(body);
  response.writeHead(status, {
    "content-type": "application/json; charset=utf-8",
    "content-length": Buffer.byteLength(text),
    // The page never loads anything remote, and nothing it renders is
    // markup: a compiler document is data.
    "content-security-policy": "default-src 'none'",
    "x-content-type-options": "nosniff",
  });
  response.end(text);
}

/**
 * Read a JSON request body, refusing one that grows past the cap.
 *
 * The check is on bytes as they arrive rather than on `content-length`,
 * which a client is free to lie about.
 */
function readBody(request) {
  return new Promise((resolve, reject) => {
    let size = 0;
    let refused = false;
    const chunks = [];
    request.on("data", (chunk) => {
      if (refused) {
        return;
      }
      size += chunk.length;
      if (size > MAX_BODY_BYTES) {
        // Keep draining rather than destroying the socket: the client is
        // owed an answer it can read, and a connection reset mid-upload
        // looks like a crash rather than a refusal.
        refused = true;
        chunks.length = 0;
        reject(new Error(`request body exceeds ${MAX_BODY_BYTES} bytes`));
        return;
      }
      chunks.push(chunk);
    });
    request.on("end", () => {
      if (refused) {
        return;
      }
      try {
        resolve(JSON.parse(Buffer.concat(chunks).toString("utf8") || "{}"));
      } catch (failure) {
        reject(new Error(`request body is not JSON: ${failure.message}`));
      }
    });
    request.on("error", (failure) => reject(failure));
  });
}

/**
 * Resolve a request path inside the static root, or null if it escapes.
 *
 * Normalizing and then checking containment is what stops `../` from
 * reaching outside the directory the service is willing to serve.
 */
export function staticPathFor(root, urlPath) {
  let decoded;
  try {
    decoded = decodeURIComponent(urlPath.split("?")[0]);
  } catch {
    return null;
  }
  // A climbing segment is refused outright rather than normalized away.
  // Normalizing first would turn `/../../etc/passwd` into a path that
  // happens to land back inside the root — safe, but silently serving
  // something nobody asked for, which is harder to reason about than a
  // flat refusal.
  if (decoded.split(/[/\\]/).includes("..")) {
    return null;
  }
  const relative = normalize(decoded);
  const candidate = resolve(join(root, relative === "/" ? "index.html" : relative));
  const rootResolved = resolve(root);
  if (candidate !== rootResolved && !candidate.startsWith(rootResolved + "/")) {
    return null;
  }
  return candidate;
}

export function createPlaygroundServer({ compiler, staticRoot, maxConcurrent = MAX_CONCURRENT }) {
  let inFlight = 0;

  async function handleCompile(request, response) {
    if (inFlight >= maxConcurrent) {
      // Refusing is the honest answer: a queue that grows without bound
      // turns one slow submission into everyone's slow submission.
      sendJson(response, 503, { error: "too many submissions in flight; try again in a moment" });
      return;
    }
    inFlight += 1;
    try {
      const body = await readBody(request);
      const result = await compileSubmission({
        compiler,
        source: body.source,
        execute: body.execute === true,
      });
      sendJson(response, 200, result);
    } catch (failure) {
      sendJson(response, 400, { error: failure.message });
    } finally {
      inFlight -= 1;
    }
  }

  async function handleStatic(request, response, pathname) {
    if (!staticRoot) {
      sendJson(response, 404, { error: "not found" });
      return;
    }
    const path = staticPathFor(staticRoot, pathname);
    if (path === null) {
      sendJson(response, 403, { error: "forbidden" });
      return;
    }
    try {
      const info = await stat(path);
      const file = info.isDirectory() ? join(path, "index.html") : path;
      const body = await readFile(file);
      response.writeHead(200, {
        "content-type": CONTENT_TYPES[extname(file)] || "application/octet-stream",
        "content-length": body.length,
        "x-content-type-options": "nosniff",
      });
      response.end(body);
    } catch {
      // A single-page app owns its own routes, so an unknown path that is
      // not an asset request falls back to the app rather than 404ing.
      if (extname(pathname) === "") {
        try {
          const body = await readFile(join(staticRoot, "index.html"));
          response.writeHead(200, { "content-type": CONTENT_TYPES[".html"], "content-length": body.length });
          response.end(body);
          return;
        } catch {
          // Falls through to the 404 below.
        }
      }
      sendJson(response, 404, { error: "not found" });
    }
  }

  return createServer((request, response) => {
    const pathname = (request.url || "/").split("?")[0];
    if (request.method === "GET" && pathname === "/api/health") {
      sendJson(response, 200, { ok: true, maxSourceBytes: MAX_SOURCE_BYTES, maxConcurrent });
      return;
    }
    if (request.method === "GET" && pathname === "/api/examples") {
      sendJson(response, 200, { examples: EXAMPLES });
      return;
    }
    if (request.method === "POST" && pathname === "/api/compile") {
      handleCompile(request, response);
      return;
    }
    if (request.method === "GET") {
      handleStatic(request, response, pathname);
      return;
    }
    sendJson(response, 405, { error: "method not allowed" });
  });
}
