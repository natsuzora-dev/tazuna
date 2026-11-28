import { defineConfig } from "drizzle-kit";

export default defineConfig({
  dialect: "sqlite",
  casing: "snake_case",
  schema: "./src/server/payments/schema.ts",
  out: "./src/server/payments/migrations",
});
