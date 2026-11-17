import { z } from "zod";
import { followUp, machine, remind, taskAdded, taskCompleted } from "./todo.ts";

export const reminder = machine({
  description: "Notify when a task is not completed within an hour after it is added",
  receives: { taskAdded, taskCompleted },
  commands: { remind },
  initial: "idle",
  states: { idle: {}, waiting: { after: ["hour"] }, reminding: {} },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ target: "waiting" }] } },
    waiting: {
      on: { taskCompleted: [{ target: "idle" }] },
      after: { hour: { delay: { hours: 1 }, onFired: [{ target: "reminding" }] } },
    },
    reminding: { sends: { remind: { onAccepted: [{ target: "idle" }] } } },
  },
});

export const counter = machine({
  description: "Report how many tasks were added an hour after the first task is added",
  context: { tasks: z.int().default(0), by: z.string().default("") },
  receives: { taskAdded },
  commands: { followUp },
  initial: "idle",
  states: { idle: {}, waiting: { after: ["hour"] }, followingUp: {} },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ target: "waiting", assign: { tasks: () => 1 } }] } },
    waiting: {
      on: { taskAdded: [{ assign: { tasks: ({ context }) => context.tasks + 1 } }] },
      after: {
        hour: {
          delay: { hours: 1 },
          onFired: [
            {
              guard: { hasManyTasks: ({ context }) => context.tasks >= 3 },
              target: "followingUp",
              assign: { by: () => "many" },
            },
            {
              guard: { hasTasks: ({ context }) => context.tasks >= 2 },
              target: "followingUp",
              assign: { by: () => "some" },
            },
          ],
        },
      },
    },
    followingUp: {
      sends: {
        followUp: { input: ({ context }) => ({ by: context.by }), onAccepted: [{ target: "idle" }] },
      },
    },
  },
});
