import { todo } from "../todo/contract.ts";
import { screen } from "./data.ts";

export const listScreen = screen({
  description: "A screen that shows the task list and closes at 11:00",
  queries: { tasks: todo.tasks },
  initial: "open",
  states: { open: {}, closed: { type: "final" } },
}).chart({
  states: {
    open: {
      shows: { tasks: {} },
      always: [
        {
          guard: {
            atEleven: ({ now }) =>
              Temporal.Instant.compare(now, Temporal.Instant.from("2026-10-25T11:00:00+09:00")) >= 0,
          },
          target: "closed",
        },
      ],
    },
  },
});
