import { at, receive, scenario, send, subscribe, unsubscribe } from "@natsuzora-dev/tazuna";
import { addTask, taskAdded, taskTitles } from "./todo.ts";

const titles = subscribe(taskTitles, {});

export const endUnopened = scenario(
  "Subscribe, unsubscribe from the open subscription, then subscribe again; no violation",
  [at("2026-10-25T09:00:00+09:00"), titles, unsubscribe(titles), subscribe(taskTitles, {})],
);

export const endUnopenedAndSubscribeTwice = scenario(
  "Unsubscribe from a subscription twice, then subscribe twice with the id s2; the second unsubscribe ends no open subscription and the second subscribe reuses s2, so test reports unopenedSubscription and reusedSubscriptionId",
  [
    at("2026-10-25T09:00:00+09:00"),
    titles,
    unsubscribe(titles),
    unsubscribe(titles),
    subscribe(taskTitles, {}, { id: "s2" }),
    subscribe(taskTitles, {}, { id: "s2" }),
  ],
);

export const addOwnTask = scenario("Add a task through the command of todo; no violation", [
  at("2026-10-25T09:00:00+09:00"),
  send(addTask, { taskId: "task-1", title: "Buy milk" }),
]);

export const receiveOwnEvent = scenario(
  "Give todo its own event, as if another service sent it; the event is in no contract of another service, so test reports unlistedEvent",
  [at("2026-10-25T09:00:00+09:00"), receive(taskAdded, { id: "task-1", title: "Buy milk" })],
);
