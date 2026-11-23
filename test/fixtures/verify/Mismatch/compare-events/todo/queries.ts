import { z } from "zod";
import { query } from "./todo.ts";

export const addedCount = query({ callers: ["client"], output: { count: z.int() } }).resolve(({ records }) => ({
  count: records.Task.size,
}));
