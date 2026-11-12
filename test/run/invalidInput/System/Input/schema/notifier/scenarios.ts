import { at, receive, scenario } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";

export const receiveAdded = scenario("Receive an added task; no violation", [
  at("2026-10-25T09:00:00+09:00"),
  receive(todo.taskAdded, { taskId: "task-1", title: "Buy milk" }),
]);

export const receiveAddedEmptyTitle = scenario(
  "Receive an added task with an empty title; the payload schema of taskAdded rejects it, so test reports eventPayloadSchema",
  [at("2026-10-25T09:00:00+09:00"), receive(todo.taskAdded, { taskId: "task-1", title: "" })],
);
