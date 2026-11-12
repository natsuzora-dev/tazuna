import { datetime, ref } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { machine, note, Task } from "./todo.ts";

export const dayNoter = machine({
  description: "Ask calendar for the next day for each open task, and write it in the task's note",
  queries: { nextDay: calendar.nextDay },
  commands: { note },
  initial: "noting",
  states: {
    noting: {
      type: "map",
      key: { taskId: ref(Task) },
      context: { day: datetime.nullable().default(null) },
      initial: "asking",
      states: { asking: {}, writing: { held: { day: datetime } }, done: {} },
    },
  },
}).chart({
  states: {
    noting: {
      items: ({ records }) => records.Task.filter((t) => t.completedAt === null).map((t) => ({ taskId: t.id })),
    },
    asking: {
      calls: {
        nextDay: {
          input: ({ now, key }) => ({ from: now, taskId: key.taskId }),
          onFulfilled: [{ target: "writing", assign: { day: ({ output }) => output.day } }],
          onRejected: [{ target: "done" }],
        },
      },
    },
    writing: {
      holds: { day: ({ context }) => context.day },
      sends: {
        note: {
          input: ({ key, held }) => ({ taskId: key.taskId, text: held.day.toString() }),
          onAccepted: [{ target: "done" }],
          onRejected: [],
        },
      },
    },
  },
});
