import { z } from "zod";
import { greet, machine, taskAdded } from "./todo.ts";

export const greeter = machine({
  description: "Count and greet at start and each time a task is added",
  context: { count: z.int().default(0) },
  receives: { taskAdded },
  commands: { greet },
  initial: "greeting",
  states: { greeting: {}, idle: {} },
}).chart({
  states: {
    greeting: {
      entry: { assign: { count: ({ context }) => context.count + 1 } },
      sends: {
        greet: {
          input: ({ context }) => ({ count: context.count }),
          onAccepted: [{ target: "idle" }],
        },
      },
    },
    idle: { on: { taskAdded: [{ target: "greeting" }] } },
  },
});
