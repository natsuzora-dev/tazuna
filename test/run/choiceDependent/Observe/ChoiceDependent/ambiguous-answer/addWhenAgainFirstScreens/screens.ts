import { calendar } from "../calendar/contract.ts";
import { todo } from "../todo/contract.ts";
import { screen } from "./data.ts";

const from = () => ({ from: Temporal.Instant.from("2026-10-25T00:00:00Z") });

export const dayScreen = screen({
  description:
    "On check, show the next day twice with the same input, and add a task when the subscription again receives its answer before the subscription nextDay",
  queries: { nextDay: calendar.nextDay, again: calendar.nextDay },
  commands: { addTask: todo.addTask },
  controls: { check: { label: "Check" } },
  initial: "idle",
  states: { idle: {}, checking: {}, adding: {} },
}).chart({
  states: {
    idle: { on: { check: [{ target: "checking" }] } },
    checking: {
      always: [
        { guard: { isAnsweredFirst: ({ shown }) => shown.again !== null && shown.nextDay === null }, target: "adding" },
      ],
      shows: { nextDay: { input: from }, again: { input: from } },
    },
    adding: {
      sends: {
        addTask: {
          input: () => ({ taskId: "task-9", title: "Check the day" }),
          onAccepted: [{ target: "idle" }],
          onRejected: [{ target: "idle" }],
        },
      },
    },
  },
});
