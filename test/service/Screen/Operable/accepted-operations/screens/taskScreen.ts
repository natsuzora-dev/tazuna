import { datetime } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { screen } from "./data.ts";

export const taskScreen = screen({
  description: "A screen that shows one task and completes it when it is open",
  queries: { task: todo.task },
  commands: { completeTask: todo.completeTask },
  controls: { complete: { label: "Complete" }, remind: { label: "Set reminder", payload: { at: datetime } } },
  initial: "open",
  states: { open: { initial: "idle", states: { idle: {}, completing: {}, completed: {} } } },
}).chart({
  offers: {
    complete: ({ shown }) => (shown.task?.isCompleted === false ? [{}] : []),
    remind: () => [{ at: Temporal.Instant.from("2026-10-25T03:00:00Z") }],
  },
  states: {
    open: { shows: { task: {} } },
    idle: { on: { complete: [{ target: "completing" }], remind: [] } },
    completing: {
      sends: {
        completeTask: {
          input: () => ({ taskId: "task-1" }),
          onAccepted: [{ target: "completed" }],
          onRejected: [{ target: "idle" }],
        },
      },
    },
    completed: {
      offers: { complete: () => [] },
      always: [{ guard: { isShownCompleted: ({ shown }) => shown.task?.isCompleted === true }, target: "idle" }],
    },
  },
});
