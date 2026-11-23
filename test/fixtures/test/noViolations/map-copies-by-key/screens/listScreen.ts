import { any } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { todo } from "../todo/contract.ts";
import { screen } from "./data.ts";

export const listScreen = screen({
  description: "A screen that shows the task list and completes a task per row",
  queries: { tasks: todo.tasks },
  commands: { completeTask: todo.completeTask },
  controls: {
    complete: { label: "Complete", payload: { taskId: z.string() } },
    completeAll: { label: "Complete all" },
  },
  initial: "showing",
  states: {
    showing: {
      initial: "rows",
      states: {
        rows: { type: "map", key: { taskId: z.string() }, initial: "idle", states: { idle: {}, completing: {} } },
      },
    },
  },
}).chart({
  offers: { complete: any, completeAll: any },
  states: {
    showing: { shows: { tasks: {} } },
    rows: { items: ({ shown }) => (shown.tasks?.taskIds ?? []).map((taskId) => ({ taskId })) },
    idle: { on: { complete: [{ target: "completing" }], completeAll: [{ target: "completing" }] } },
    completing: {
      sends: {
        completeTask: { input: ({ key }) => key, onAccepted: [{ target: "idle" }], onRejected: [{ target: "idle" }] },
      },
    },
  },
});
