import { at, receive, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask, taskAdded } from "./todo.ts";

export const addOwnTask = scenario("Add a task through the command of todo; no violation", [
  at("2026-10-25T09:00:00+09:00"),
  send(addTask, { taskId: "task-1", title: "Buy milk" }),
]);

export const receiveOwnEvent = scenario(
  "Give todo its own event, as if another service sent it; the event is in no contract of another service, so test reports unlistedEvent",
  [at("2026-10-25T09:00:00+09:00"), receive(taskAdded, { id: "task-1", title: "Buy milk" })],
);
