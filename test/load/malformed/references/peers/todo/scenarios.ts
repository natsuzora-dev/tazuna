import { at, elsewhere, receive, scenario, send } from "@natsuzora-dev/tazuna";
import { notifier } from "../notifier/contract.ts";
import { addTask, taskAdded } from "./todo.ts";

export const givesOwnEventToPeer = scenario(
  "Give notifier a state and an input elsewhere that receive todo's own event; check reports ownMessageToPeer for each",
  [
    at("2026-10-25T10:00:00+09:00"),
    elsewhere(notifier, receive(taskAdded, { taskId: "task-1" })),
    send(addTask, { taskId: "task-1", title: "Buy milk" }),
  ],
  { given: { notifier: notifier.states.announcedMilk } },
);

export const givesOwnAnswerToPeer = scenario(
  "Give notifier a state that answers its request to todo; check reports ownMessageToPeer",
  [at("2026-10-25T10:00:00+09:00"), send(addTask, { taskId: "task-1", title: "Buy milk" })],
  { given: { notifier: notifier.states.addedMilk } },
);
