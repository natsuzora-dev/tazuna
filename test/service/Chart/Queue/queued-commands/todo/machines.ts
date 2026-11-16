import { z } from "zod";
import { machine, schedule, taskAdded } from "./todo.ts";

export const scheduler = machine({
  description: "Schedule a notification for each added task",
  context: { taskId: z.string().nullable().default(null) },
  receives: { taskAdded },
  commands: { schedule },
  initial: "idle",
  states: { idle: {}, scheduling: { held: { taskId: z.string() } } },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ target: "scheduling", assign: { taskId: ({ payload }) => payload.taskId } }] } },
    scheduling: {
      holds: { taskId: ({ context }) => context.taskId },
      sends: {
        schedule: { input: ({ held }) => ({ taskId: held.taskId }), onAccepted: [{ target: "idle" }] },
      },
    },
  },
});
