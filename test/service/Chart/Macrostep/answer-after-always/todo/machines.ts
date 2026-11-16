import { calendar } from "../calendar/contract.ts";
import { machine, noteAnswer, taskAdded } from "./todo.ts";

export const planner = machine({
  description:
    "Ask calendar for the next day when a task is added and record the answer, stop asking at 11:00, and ask again when the next task is added",
  receives: { taskAdded },
  queries: { nextDay: calendar.nextDay },
  commands: { noteAnswer },
  initial: "idle",
  states: { idle: {}, asking: {}, noting: {}, gaveUp: {} },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ target: "asking" }] } },
    asking: {
      always: [
        {
          guard: {
            late: ({ now }) => Temporal.Instant.compare(now, Temporal.Instant.from("2026-10-25T02:00:00Z")) >= 0,
          },
          target: "gaveUp",
        },
      ],
      calls: {
        nextDay: {
          input: ({ now }) => ({ from: now }),
          onFulfilled: [{ target: "noting" }],
          onRejected: [{ target: "noting" }],
        },
      },
    },
    noting: { sends: { noteAnswer: { onAccepted: [{ target: "idle" }] } } },
    gaveUp: { on: { taskAdded: [{ target: "asking" }] } },
  },
});
