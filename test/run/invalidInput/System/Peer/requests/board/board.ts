import { service } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";

export const { screen } = service({ description: "Show the tasks" });

export const boardScreen = screen({
  description: "A screen that shows the tasks",

  queries: { tasks: todo.tasks },

  initial: "listing",
  states: { listing: {} },
}).chart({ states: { listing: { shows: { tasks: {} } } } });
