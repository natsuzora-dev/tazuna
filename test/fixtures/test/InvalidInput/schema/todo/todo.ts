import { externalService } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, event, contract } = externalService({ name: "todo", description: "Keep the tasks" });

export const taskAdded = event({ payload: { taskId: z.string(), title: z.string().min(1) } });

export const addTask = command({
  callers: ["planner"],
  input: { taskId: z.string(), title: z.string().min(1) },
  emits: [taskAdded],
  rejects: ["already-exists", "requires", "unavailable"],
  requires: { short: ({ input }) => input.title.length <= 100 },
});
