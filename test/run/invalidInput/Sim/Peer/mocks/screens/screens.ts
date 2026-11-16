import { service } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";

export const { screen } = service({ description: "Show the tasks" });

export const listScreen = screen({
  description: "A screen that shows the titles of the tasks",
  queries: { taskTitles: todo.taskTitles },
  initial: "open",
  states: { open: {} },
}).chart({ states: { open: { shows: { taskTitles: {} } } } });
