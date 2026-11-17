import { z } from "zod";
import { machine, remind, taskAdded } from "./planner.ts";

export const reminder = machine({
  description:
    "Notify two hours after 10:00, and delay the notification by an hour each time a task is added. Adding a task whose taskId is now sets the notification time to 10:00",
  context: { hours: z.int().default(2) },
  receives: { taskAdded },
  commands: { remind },
  initial: "waiting",
  states: { waiting: { after: ["due"] }, reminding: {}, done: { type: "final" } },
}).chart({
  states: {
    waiting: {
      on: {
        taskAdded: [
          { assign: { hours: ({ context, payload }) => (payload.taskId === "now" ? 0 : context.hours + 1) } },
        ],
      },
      after: {
        due: {
          at: ({ context }) => Temporal.Instant.from("2026-10-25T01:00:00Z").add({ hours: context.hours }),
          onFired: [{ target: "reminding" }],
        },
      },
    },
    reminding: { sends: { remind: { onAccepted: [{ target: "done" }] } } },
  },
});
