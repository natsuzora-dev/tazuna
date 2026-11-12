import { tanstackStart } from "@tanstack/react-start/plugin/vite";
import basicSsl from "@vitejs/plugin-basic-ssl";
import viteReact from "@vitejs/plugin-react";
import { nitro } from "nitro/vite";
import { defaultClientConditions, defaultServerConditions, defineConfig } from "vite";

export default defineConfig({
  plugins: [tanstackStart(), nitro({ plugins: ["plugins/startup.ts"] }), viteReact(), basicSsl()],
  resolve: { conditions: ["tazuna:source", ...defaultClientConditions] },
  ssr: { resolve: { conditions: ["tazuna:source", ...defaultServerConditions] } },
  server: { port: 3000, strictPort: true },
});
