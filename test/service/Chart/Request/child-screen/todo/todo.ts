import { service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { query, contract } = service({ description: "Keep tasks" });

export const tasks = query({
  input: { filter: z.enum(["open", "all"]) },
  output: { taskIds: z.array(z.string()) },
}).resolve(() => ({ taskIds: [] }));

export const taskCount = query({
  input: { filter: z.enum(["open", "all"]) },
  output: { count: z.int() },
}).resolve(() => ({ count: 0 }));
