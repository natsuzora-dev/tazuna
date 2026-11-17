import { z } from "zod";
import { machine, remind, taskAdded } from "./todo.ts";

export const reminder = machine({
  description: "Report an hour after a task is added and waiting is entered, and reenter active once at 11:00",
  receives: { taskAdded },
  commands: { remind },
  context: { restarted: z.boolean().default(false) },
  initial: "idle",
  states: { idle: {}, active: { initial: "waiting", states: { waiting: {} } }, reminding: {} },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ target: "active" }] } },
    active: {
      always: [
        {
          guard: {
            atEleven: ({ now, context }) =>
              !context.restarted &&
              Temporal.Instant.compare(now, Temporal.Instant.from("2026-10-25T11:00:00+09:00")) >= 0,
          },
          target: "active",
          reenter: true,
          assign: { restarted: () => true },
        },
      ],
    },
    waiting: { after: { hour: { delay: { hours: 1 }, onFired: [{ target: "reminding" }] } } },
    reminding: { sends: { remind: { onAccepted: [] } } },
  },
});
