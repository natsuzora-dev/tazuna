import { drizzle } from "drizzle-orm/node-sqlite";

const fileName = process.env["DB_FILE_NAME"];
if (fileName === undefined) throw new Error("DB_FILE_NAME is not set");

export const db = drizzle(fileName);
