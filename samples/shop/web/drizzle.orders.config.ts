import { defineConfig } from "drizzle-kit";

export default defineConfig({
  dialect: "sqlite",
  casing: "snake_case",
  schema: "./src/server/orders/schema.ts",
  out: "./src/server/orders/migrations",
});
