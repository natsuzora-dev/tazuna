import { at, elsewhere, receive, scenario, send } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { announce } from "./notifier.ts";

export const announcesAdded = scenario(
  "Receive taskAdded for the task that another caller adds; todo's run of the derived inputs has a snapshot but no trace, so verify reports missingTrace",
  [
    at("2026-10-25T10:00:00+09:00"),
    elsewhere(todo, send(todo.addTask, { taskId: "task-1", title: "Buy milk" })),
    receive(todo.taskAdded, { taskId: "task-1" }),
  ],
);

export const announcesDirectly = scenario(
  "Announce without todo; no todo run has a snapshot, so verify skips the trace announcesDirectly.todo.jsonl, and reports announcesDirectly.notifier.jsonl, which names no other service's run, as unknownScenario",
  [at("2026-10-25T10:00:00+09:00"), send(announce, { taskId: "task-1" })],
);
