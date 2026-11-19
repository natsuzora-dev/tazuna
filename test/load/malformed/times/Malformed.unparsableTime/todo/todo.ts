import { service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { query, contract, scenario } = service({ name: "todo", description: "Answer the task count" });

export const taskCount = query({ output: { count: z.int() } }).resolve(() => ({ count: 0 }));

export const todo = contract({ taskCount });
