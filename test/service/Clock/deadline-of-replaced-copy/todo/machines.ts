import { ref } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { machine, remind, Task } from "./todo.ts";

export const perTask = machine({
  description: "In each task copy, report an hour after the copy enters waiting, and reenter rows once at 11:00",
  commands: { remind },
  context: { restarted: z.boolean().default(false) },
  initial: "rows",
  states: {
    rows: {
      type: "map",
      key: { taskId: ref(Task) },
      initial: "waiting",
      states: { waiting: { after: ["hour"] }, reminding: {} },
    },
  },
}).chart({
  states: {
    rows: {
      items: ({ records }) => records.Task.map((t) => ({ taskId: t.id })),
      always: [
        {
          guard: {
            atEleven: ({ now, context }) =>
              !context.restarted &&
              Temporal.Instant.compare(now, Temporal.Instant.from("2026-10-25T11:00:00+09:00")) >= 0,
          },
          target: "rows",
          reenter: true,
          assign: { restarted: () => true },
        },
      ],
    },
    waiting: { after: { hour: { delay: { hours: 1 }, onFired: [{ target: "reminding" }] } } },
    reminding: { sends: { remind: { input: ({ key }) => key, onAccepted: [], onRejected: [] } } },
  },
});
