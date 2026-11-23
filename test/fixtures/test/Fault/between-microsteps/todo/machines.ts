import { z } from "zod";
import { machine, taskAdded } from "./todo.ts";

export const tally = machine({
  description: "Count the added tasks and keep the shown count in line",
  context: { added: z.int().default(0), shown: z.int().default(0) },
  receives: { taskAdded },
  initial: "idle",
  states: { idle: {}, updating: {} },
  invariants: { inSync: ({ context }) => context.added === context.shown },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ target: "updating", assign: { added: ({ context }) => context.added + 1 } }] } },
    updating: { always: [{ target: "idle", assign: { shown: ({ context }) => context.added } }] },
  },
});
