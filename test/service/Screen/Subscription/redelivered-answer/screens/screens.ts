import { any } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { screen } from "./data.ts";

export const counterScreen = screen({
  description: "A screen that shows the task count and reports it",
  queries: { taskCount: todo.taskCount },
  commands: { note: todo.note },
  controls: { report: { label: "Report" } },
  initial: "showing",
  states: { showing: { initial: "idle", states: { idle: {}, reporting: {} } } },
}).chart({
  offers: { report: any },
  states: {
    showing: { shows: { taskCount: {} } },
    idle: { on: { report: [{ target: "reporting" }] } },
    reporting: {
      sends: {
        note: {
          input: ({ shown }) => ({ count: shown.taskCount?.count ?? -1 }),
          onAccepted: [{ target: "idle" }],
          onRejected: [{ target: "idle" }],
        },
      },
    },
  },
});
