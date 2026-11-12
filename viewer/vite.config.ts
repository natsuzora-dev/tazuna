import { defaultClientConditions, defineConfig } from "vite";

export default defineConfig({
  root: import.meta.dirname,
  base: "./",
  resolve: { conditions: ["tazuna:source", ...defaultClientConditions] },
  build: {
    outDir: "../dist/viewer",
    emptyOutDir: true,
    rolldownOptions: {
      // The viewer runs only in the browser and has no React Server Components "use client" boundary.
      onwarn(warning, warn) {
        if (warning.code !== "MODULE_LEVEL_DIRECTIVE") warn(warning);
      },
    },
  },
  // The elkjs worker also assigns module.exports, so it builds as an ES module worker, not an IIFE.
  worker: { format: "es" },
});
