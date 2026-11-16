import { service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { query } = service({ description: "Keep tasks" });

export const tasks = query({
  input: { filter: z.enum(["open", "all"]) },
  output: { taskIds: z.array(z.string()) },
}).resolve(() => ({ taskIds: [] }));

export const taskCount = query({ output: { count: z.int() } }).resolve(() => ({ count: 0 }));
