import { z } from "zod";
import { query } from "./todo.ts";

export const addedCount = query({ output: { count: z.number() } }).resolve(({ records }) => ({
  count: records.Task.size,
}));
