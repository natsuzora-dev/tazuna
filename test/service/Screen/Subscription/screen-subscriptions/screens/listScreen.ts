import { z } from "zod";
import { todo } from "../todo/contract.ts";
import { screen } from "./data.ts";

export const listScreen = screen({
  description: "A screen that shows the task list and the task count",
  context: { filter: z.enum(["open", "all"]).default("open") },
  queries: { tasks: todo.tasks, taskCount: todo.taskCount, allTasks: todo.tasks },
  controls: {
    showAll: { label: "Show all" },
    reload: { label: "Reload" },
    peek: { label: "Briefly show all tasks" },
  },
  initial: "open",
  states: { open: { initial: "loading", states: { loading: {}, ready: {}, peeking: {} } } },
}).chart({
  on: { reload: [{ target: "open" }] },
  states: {
    open: { shows: { tasks: { input: ({ context }) => ({ filter: context.filter }) }, taskCount: {} } },
    loading: {
      always: [
        { guard: { isLoaded: ({ shown }) => shown.tasks !== null && shown.taskCount !== null }, target: "ready" },
      ],
    },
    ready: {
      on: { showAll: [{ assign: { filter: () => "all" } }], peek: [{ target: "peeking" }] },
    },
    peeking: { always: [{ target: "ready" }], shows: { allTasks: { input: () => ({ filter: "all" }) } } },
  },
});
