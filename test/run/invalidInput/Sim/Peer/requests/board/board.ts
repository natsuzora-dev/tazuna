import { service } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";

export const { screen, contract } = service({ description: "Show the tasks" });

export const boardScreen = screen({
  description: "A screen that shows the tasks until todo adds the task close",

  receives: { taskAdded: todo.taskAdded },
  queries: { tasks: todo.tasks },
  initial: "listing",
  states: { listing: {}, closed: {} },
}).chart({
  states: {
    listing: {
      on: { taskAdded: [{ guard: { closing: ({ payload }) => payload.taskId === "close" }, target: "closed" }] },
      shows: { tasks: {} },
    },
  },
});
