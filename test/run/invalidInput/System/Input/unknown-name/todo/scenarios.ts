import { at, receive, scenario, send, subscribe, unsubscribe } from "@natsuzora-dev/tazuna";
import { addTask, taskAdded, taskTitles } from "./todo.ts";

export const endUnopened = scenario(
  "Subscribe, unsubscribe from the open subscription, then subscribe with another id; no violation",
  [
    at("2026-10-25T09:00:00+09:00"),
    subscribe(taskTitles, {}, { id: "s1" }),
    unsubscribe("s1"),
    subscribe(taskTitles, {}, { id: "s2" }),
  ],
);

export const endUnopenedAndSubscribeTwice = scenario(
  "Unsubscribe from s1, which is not open, then subscribe twice with the id s2; test reports subscriptionNotOpen and subscriptionOpen",
  [
    at("2026-10-25T09:00:00+09:00"),
    unsubscribe("s1"),
    subscribe(taskTitles, {}, { id: "s2" }),
    subscribe(taskTitles, {}, { id: "s2" }),
  ],
);

export const addOwnTask = scenario("Add a task through the command of todo; no violation", [
  at("2026-10-25T09:00:00+09:00"),
  send(addTask, { taskId: "task-1", title: "Buy milk" }),
]);

export const receiveOwnEvent = scenario(
  "Give todo its own event, as if another service sent it; the event is in no contract of another service, so test reports notInContract",
  [at("2026-10-25T09:00:00+09:00"), receive(taskAdded, { id: "task-1", title: "Buy milk" })],
);
