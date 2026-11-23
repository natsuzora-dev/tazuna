import { externalService } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, query, contract } = externalService({ name: "todo", description: "Keep tasks" });

export const completeTask = command({
  callers: ["screens"],
  input: { taskId: z.string() },
  emits: [],
  rejects: ["invalid-input", "requires", "unavailable", "reused-id"],
});

export const tasks = query({
  callers: ["screens"],
  output: { taskIds: z.array(z.string()) },
  rejects: ["invalid-input", "requires", "unavailable"],
});
