import { todo } from "../todo/contract.ts";
import { screen } from "./data.ts";

export const listScreen = screen({
  description:
    "A screen that shows tasks, enters leaving on the operation leave, enters cleared when shown.tasks becomes null, and goes back to viewing and shows the tasks again on the operation back",
  queries: { tasks: todo.tasks },
  controls: { leave: { label: "Leave" }, back: { label: "Back" } },
  initial: "viewing",
  states: { viewing: {}, leaving: {}, cleared: {} },
  invariants: { notLeftOver: ({ active }) => !active.leaving },
}).chart({
  states: {
    viewing: { on: { leave: [{ target: "leaving" }] }, shows: { tasks: {} } },
    leaving: { always: [{ guard: { cleared: ({ shown }) => shown.tasks === null }, target: "cleared" }] },
    cleared: { on: { back: [{ target: "viewing" }] } },
  },
});
