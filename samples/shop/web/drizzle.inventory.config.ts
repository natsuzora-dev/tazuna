import { defineConfig } from "drizzle-kit";

export default defineConfig({
  dialect: "sqlite",
  casing: "snake_case",
  schema: "./src/server/inventory/schema.ts",
  out: "./src/server/inventory/migrations",
});
