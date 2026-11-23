import { externalService } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, query, contract } = externalService({ name: "todo", description: "Keep tasks" });

export const completeTask = command({
  callers: ["screens"],
  input: { taskId: z.string() },
  emits: [],
  rejects: ["invalid-input", "requires", "unavailable", "reused-id"],
});

export const task = query({
  callers: ["screens"],
  output: { isCompleted: z.boolean() },
  rejects: ["invalid-input", "requires", "unavailable"],
});
