import { defineConfig } from "vite";
import react from "@vitejs/plugin-react";

// The API is same-origin in production — the container serves both — so the
// only proxying needed is during development, when Vite serves the page and
// the API runs separately.
export default defineConfig({
  plugins: [react()],
  server: {
    proxy: {
      "/api": "http://127.0.0.1:8080",
    },
  },
  build: {
    outDir: "dist",
    // Monaco is large and splits well; leaving it in its own chunk keeps
    // the first paint from waiting on the editor.
    chunkSizeWarningLimit: 2048,
  },
});
