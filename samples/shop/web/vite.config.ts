import { tanstackRouter } from "@tanstack/router-plugin/vite";
import react from "@vitejs/plugin-react";
import { defineConfig } from "vitest/config";

export default defineConfig({
  plugins: [
    tanstackRouter({
      target: "react",
      routesDirectory: "src/client/routes",
      generatedRouteTree: "src/client/routeTree.gen.ts",
      autoCodeSplitting: true,
    }),
    react(),
  ],
  server: { proxy: { "/api": "http://localhost:3000" } },
  build: { outDir: "dist" },
  test: { include: ["src/**/*.test.ts"] },
});
