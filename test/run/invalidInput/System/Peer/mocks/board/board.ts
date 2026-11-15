import { service } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";

export const { screen } = service({ description: "Complete the tasks" });

export const boardScreen = screen({
  description: "A screen that shows the tasks and completes one",
  context: { taskId: todo.TaskId.nullable().default(null) },
  queries: { tasks: todo.tasks },
  commands: { completeTask: todo.completeTask },
  controls: { complete: { label: "Complete", payload: { taskId: todo.TaskId } } },
  initial: "listing",
  states: { listing: {}, completing: { held: { taskId: todo.TaskId } } },
}).chart({
  offers: { complete: ({ shown }) => (shown.tasks?.tasks ?? []).map((t) => ({ taskId: t.taskId })) },
  states: {
    listing: {
      shows: { tasks: {} },
      on: { complete: [{ target: "completing", assign: { taskId: ({ payload }) => payload.taskId } }] },
    },
    completing: {
      holds: { taskId: ({ context }) => context.taskId },
      sends: {
        completeTask: {
          input: ({ held }) => ({ taskId: held.taskId }),
          onAccepted: [{ target: "listing" }],
          onRejected: [{ target: "listing" }],
        },
      },
    },
  },
});
