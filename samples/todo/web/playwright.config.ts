import { defineConfig, devices } from "@playwright/test";

export default defineConfig({
  testDir: "test/e2e",
  fullyParallel: true,
  forbidOnly: true,
  reporter: "list",
  use: { ...devices["Desktop Chrome"], ignoreHTTPSErrors: true },
});
