import { external } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { scenario } from "./notifier.ts";

const given = { start: "2026-10-25T09:00:00+09:00", records: {}, peers: { todo: external(todo) } } as const;

export const receiveAdded = scenario("Receive an added task; no violation", {
  given,
  when: (w) => {
    w.net.deliver(w.peer.todo.emit(todo.taskAdded, { taskId: "task-1", title: "Buy milk" }, { resultOf: null }));
  },
  then: () => [],
});

export const receiveAddedEmptyTitle = scenario(
  "Receive an added task with an empty title; the payload schema of taskAdded rejects it, so test reports eventPayloadSchema",
  {
    given,
    when: (w) => {
      w.net.deliver(w.peer.todo.emit(todo.taskAdded, { taskId: "task-1", title: "" }, { resultOf: null }));
    },
    then: () => [],
  },
);
