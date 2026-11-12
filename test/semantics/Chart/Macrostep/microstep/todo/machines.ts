import { z } from "zod";
import { machine, remind, taskAdded } from "./todo.ts";

export const reminder = machine({
  description: "Notify, when a task is added, whether the tasks have been counted",
  context: { count: z.int().default(0) },
  receives: { taskAdded },
  commands: { remind },
  initial: "running",
  states: {
    running: {
      type: "parallel",
      states: {
        reminding: {
          initial: "idle",
          states: { idle: {}, checking: {}, beforeCount: {}, afterCount: {}, done: { type: "final" } },
        },
        counting: { initial: "waiting", states: { waiting: {}, counted: { type: "final" } } },
      },
    },
  },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ target: "checking" }] } },
    checking: {
      always: [
        { guard: { isUncounted: ({ context }) => context.count === 0 }, target: "beforeCount" },
        { target: "afterCount" },
      ],
    },
    beforeCount: {
      sends: { remind: { input: () => ({ by: "beforeCount" }), onAccepted: [{ target: "done" }] } },
    },
    afterCount: {
      sends: { remind: { input: () => ({ by: "afterCount" }), onAccepted: [{ target: "done" }] } },
    },
    waiting: { on: { taskAdded: [{ target: "counted", assign: { count: ({ context }) => context.count + 1 } }] } },
  },
});
