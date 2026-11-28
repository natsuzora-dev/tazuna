import { defineConfig, devices } from "@playwright/test";

const port = 4173;

export default defineConfig({
  testDir: "e2e",
  // One server holds the shop the tests share, so the tests run one at a time.
  workers: 1,
  forbidOnly: Boolean(process.env.CI),
  reporter: process.env.CI ? "github" : "list",
  use: { baseURL: `http://localhost:${port}`, trace: "retain-on-failure" },
  projects: [{ name: "chromium", use: { ...devices["Desktop Chrome"] } }],
  webServer: {
    command: "vite build && node e2e/server.ts",
    url: `http://localhost:${port}/api/session`,
    reuseExistingServer: !process.env.CI,
    env: { PORT: String(port), TRACE_DIR: "e2e-traces" },
  },
});
