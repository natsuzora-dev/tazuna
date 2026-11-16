import { any } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { todo } from "../todo/contract.ts";
import { screen } from "./data.ts";

export const rowScreen = screen({
  description: "A screen that completes only the tasks whose copies are in idle",
  queries: { openTasks: todo.openTasks },
  commands: { completeTask: todo.completeTask },
  controls: { complete: { label: "Complete", payload: { taskId: z.string() } } },
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
  offers: { complete: any },
  states: {
    showing: { shows: { openTasks: {} } },
    rows: { items: ({ shown }) => (shown.openTasks?.taskIds ?? []).map((taskId) => ({ taskId })) },
    idle: { offers: { complete: ({ key }) => [key] }, on: { complete: [{ target: "completing" }] } },
    completing: {
      offers: { complete: () => [] },
      sends: {
        completeTask: { input: ({ key }) => key, onAccepted: [{ target: "idle" }], onRejected: [{ target: "idle" }] },
      },
    },
  },
});
