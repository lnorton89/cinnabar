#!/usr/bin/env node
// Entry point: read the environment, bind, serve.
//
// The address defaults to every interface because this is meant to run
// inside a container that publishes one port. That is the opposite of the
// compiler's own `cinnabar playground`, which refuses anything but
// loopback because it runs on a developer's machine with no container
// around it. Both are right for where they run, and this file says so out
// loud because the difference is a security boundary.

import { createPlaygroundServer } from "./server.js";

const compiler = process.env.CINNABAR_BIN || "cinnabar";
const staticRoot = process.env.PLAYGROUND_STATIC_ROOT || null;
const port = Number(process.env.PORT || 8080);
const host = process.env.HOST || "0.0.0.0";

const server = createPlaygroundServer({ compiler, staticRoot });
server.listen(port, host, () => {
  console.log(`cinnabar playground listening on ${host}:${port} (compiler: ${compiler})`);
});

for (const signal of ["SIGINT", "SIGTERM"]) {
  process.on(signal, () => {
    server.close(() => process.exit(0));
  });
}
