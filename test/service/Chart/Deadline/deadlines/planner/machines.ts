import { parseInstant } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { machine, remind, taskAdded } from "./planner.ts";

export const reminder = machine({
  description:
    "Notify two hours after 10:00, and delay the notification by an hour each time a task is added, by entering waiting again. Adding a task whose taskId is now sets the notification time to 10:00",
  context: { hours: z.int().default(2) },
  receives: { taskAdded },
  commands: { remind },
  initial: "waiting",
  states: { waiting: {}, reminding: {}, done: { type: "final" } },
}).chart({
  states: {
    waiting: {
      on: {
        taskAdded: [
          {
            target: "waiting",
            reenter: true,
            assign: { hours: ({ context, payload }) => (payload.taskId === "now" ? 0 : context.hours + 1) },
          },
        ],
      },
      after: {
        due: {
          at: ({ context }) => parseInstant("2026-10-25T01:00:00Z") + context.hours * 3_600_000,
          onFired: [{ target: "reminding" }],
        },
      },
    },
    reminding: { sends: { remind: { onAccepted: [{ target: "done" }] } } },
  },
});

export const fixedReminder = machine({
  description:
    "Notify two hours after 10:00. Adding a task changes the hours without entering waiting again, so the notification time stays",
  context: { hours: z.int().default(2) },
  receives: { taskAdded },
  commands: { remind },
  initial: "waiting",
  states: { waiting: {}, reminding: {}, done: { type: "final" } },
}).chart({
  states: {
    waiting: {
      on: { taskAdded: [{ assign: { hours: ({ context }) => context.hours + 1 } }] },
      after: {
        due: {
          at: ({ context }) => parseInstant("2026-10-25T01:00:00Z") + context.hours * 3_600_000,
          onFired: [{ target: "reminding" }],
        },
      },
    },
    reminding: { sends: { remind: { onAccepted: [{ target: "done" }] } } },
  },
});
