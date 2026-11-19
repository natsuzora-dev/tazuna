import { datetime } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { machine, noteDay, taskAdded, taskCompleted } from "./todo.ts";

export const dayNoter = machine({
  description: "Ask calendar for the next day each time a task is added, and record the answer",
  receives: { taskAdded, taskCompleted },
  queries: { nextDay: calendar.nextDay },
  commands: { noteDay },
  initial: "waiting",
  states: { waiting: {}, asking: {}, noting: { held: { day: datetime } } },
}).chart({
  states: {
    waiting: { on: { taskAdded: [{ target: "asking" }] } },
    asking: {
      on: { taskCompleted: [{ target: "waiting" }] },
      calls: {
        nextDay: {
          input: ({ now }) => ({ from: now }),
          onFulfilled: [{ target: "noting", with: { day: ({ output }) => output.day } }],
          onRejected: [{ target: "waiting" }],
        },
      },
    },
    noting: {
      sends: {
        noteDay: {
          input: ({ held }) => ({ day: held.day }),
          onAccepted: [{ target: "waiting" }],
        },
      },
    },
  },
});
