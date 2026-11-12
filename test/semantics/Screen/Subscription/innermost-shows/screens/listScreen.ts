import { todo } from "../todo/contract.ts";
import { screen } from "./data.ts";

export const listScreen = screen({
  description: "A screen that shows the open tasks, or all tasks after showAll",
  queries: { tasks: todo.tasks },
  controls: { showAll: { label: "Show all" } },
  initial: "open",
  states: { open: { initial: "someTasks", states: { someTasks: {}, allTasks: {} } } },
}).chart({
  states: {
    open: { shows: { tasks: { input: () => ({ filter: "open" }) } } },
    someTasks: { on: { showAll: [{ target: "allTasks" }] } },
    allTasks: { shows: { tasks: { input: () => ({ filter: "all" }) } } },
  },
});
