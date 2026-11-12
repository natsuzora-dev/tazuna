import { tanstackStart } from "@tanstack/react-start/plugin/vite";
import { defaultServerConditions } from "vite";
import { defineConfig } from "vitest/config";

export default defineConfig({
  plugins: [tanstackStart()],
  ssr: { resolve: { conditions: ["tazuna:source", ...defaultServerConditions] } },
  test: {
    include: ["test/*.test.ts"],
    // TanStack Start's server imports virtual modules that its plugin makes, so Vite, not Node, must load it.
    server: { deps: { inline: [/@tanstack\/(react-)?start/] } },
    env: { DB_FILE_NAME: ":memory:" },
    sequence: { shuffle: true },
  },
});
