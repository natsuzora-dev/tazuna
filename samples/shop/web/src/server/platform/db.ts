import Database from "better-sqlite3";
import { drizzle } from "drizzle-orm/better-sqlite3";
import { migrate } from "drizzle-orm/better-sqlite3/migrator";

/** Opens a service's own SQLite database (`:memory:` in tests) and brings its schema up to date. */
export function openDatabase<TSchema extends Record<string, unknown>>(
  file: string,
  schema: TSchema,
  migrationsFolder: string,
) {
  const client = new Database(file);
  client.pragma("journal_mode = WAL");
  client.pragma("foreign_keys = ON");
  const db = drizzle({ client, schema, casing: "snake_case" });
  migrate(db, { migrationsFolder });
  return db;
}
