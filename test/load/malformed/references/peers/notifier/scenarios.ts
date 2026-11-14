import { at, elsewhere, receive, scenario, send } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { todo } from "../todo/contract.ts";
import { announce } from "./notifier.ts";

export const givesUnknownServices = scenario(
  "Give a state to a service that the spec does not have, to the scenario's own service, and to an external service; check reports unknownPeer for each",
  [at("2026-10-25T10:00:00+09:00"), send(announce, { taskId: "task-1" })],
  { given: { nobody: todo.states.milk, notifier: todo.states.milk, calendar: todo.states.milk } },
);

export const givesUnlistedState = scenario(
  "Give todo a state that its contract does not list; check reports unlistedState",
  [at("2026-10-25T10:00:00+09:00"), receive(todo.taskAdded, { taskId: "task-1" })],
  {
    given: { todo: [at("2026-10-25T08:00:00+09:00"), send(todo.addTask, { taskId: "task-1", title: "Buy milk" })] },
  },
);

export const addsElsewhereToNoPeer = scenario(
  "Give an input elsewhere to an external service and to an object that is not an exported contract; check reports unknownPeer for each, the latter with a null service",
  [
    at("2026-10-25T10:00:00+09:00"),
    elsewhere(calendar, send(calendar.addReminder, {})),
    elsewhere({ addTask: todo.addTask }, send(todo.addTask, { taskId: "task-1", title: "Buy milk" })),
    receive(todo.taskAdded, { taskId: "task-1" }),
  ],
);
