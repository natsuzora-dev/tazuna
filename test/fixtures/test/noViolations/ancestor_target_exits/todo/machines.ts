import { parseInstant } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { machine, remind, taskAdded } from "./todo.ts";

export const reminder = machine({
  description:
    "Report an hour after a task is added and waiting is entered, and go back to its ancestor active once at 11:00",
  receives: { taskAdded },
  commands: { remind },
  context: { restarted: z.boolean().default(false) },
  initial: "idle",
  states: { idle: {}, active: { initial: "waiting", states: { waiting: {} } }, reminding: {} },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ target: "active" }] } },
    waiting: {
      after: { hour: { delay: 3_600_000, onFired: [{ target: "reminding" }] } },
      always: [
        {
          guard: {
            atEleven: ({ now, context }) => !context.restarted && now >= parseInstant("2026-10-25T11:00:00+09:00"),
          },
          target: "active",
          assign: { restarted: () => true },
        },
      ],
    },
    reminding: { sends: { remind: { onAccepted: [] } } },
  },
});
