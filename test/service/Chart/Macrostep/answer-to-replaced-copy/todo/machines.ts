import { ref } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { calendar } from "../calendar/contract.ts";
import { machine, Task } from "./todo.ts";

export const perTask = machine({
  description: "Ask calendar for the next day in each task copy, and reenter rows once at 11:00",
  queries: { nextDay: calendar.nextDay },
  context: { restarted: z.boolean().default(false) },
  initial: "rows",
  states: {
    rows: { type: "map", key: { taskId: ref(Task) }, initial: "asking", states: { asking: {}, answered: {} } },
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
    asking: {
      calls: {
        nextDay: { input: ({ now }) => ({ from: now }), onFulfilled: [{ target: "answered" }], onRejected: [] },
      },
    },
  },
});
