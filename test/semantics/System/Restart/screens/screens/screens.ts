import { todo } from "../todo/contract.ts";
import { screen } from "./data.ts";

export const taskListScreen = screen({
  description: "A screen that shows the list of tasks",
  queries: { tasks: todo.tasks },
  controls: { close: { label: "Close" } },
  initial: "showing",
  states: { showing: {}, closed: { type: "final" } },
}).chart({ states: { showing: { on: { close: [{ target: "closed" }] }, shows: { tasks: {} } } } });

export const homeScreen = screen({
  description: "A home screen that opens the task list",
  screens: { taskList: taskListScreen },
  controls: { openList: { label: "Open list" } },
  initial: "home",
  states: { home: {}, listing: {} },
}).chart({
  states: {
    home: { on: { openList: [{ target: "listing" }] } },
    listing: { opens: { taskList: { modal: true, onDone: [{ target: "home" }] } } },
  },
});
