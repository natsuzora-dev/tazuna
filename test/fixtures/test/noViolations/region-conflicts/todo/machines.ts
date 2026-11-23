import { z } from "zod";
import { machine, reportCount, taskAdded } from "./todo.ts";

export const tracker = machine({
  description:
    "Count the tasks in the region counting of the parallel state tracking, remember the last added task in the region remembering, and record both",
  context: { count: z.int().default(0), lastTaskId: z.string().default("") },
  receives: { taskAdded },
  commands: { reportCount },
  initial: "tracking",
  states: {
    tracking: {
      type: "parallel",
      states: {
        counting: {},
        remembering: { initial: "waiting", states: { waiting: {}, reporting: {} } },
      },
    },
  },
}).chart({
  states: {
    counting: {
      on: {
        taskAdded: [{ target: "counting", reenter: false, assign: { count: ({ context }) => context.count + 1 } }],
      },
    },
    waiting: { on: { taskAdded: [{ target: "reporting", assign: { lastTaskId: ({ payload }) => payload.taskId } }] } },
    reporting: {
      sends: {
        reportCount: {
          input: ({ context }) => ({ count: context.count, lastTaskId: context.lastTaskId }),
          onAccepted: [{ target: "waiting" }],
        },
      },
    },
  },
});
