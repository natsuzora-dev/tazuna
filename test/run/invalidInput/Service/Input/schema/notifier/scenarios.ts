import { external, parseInstant } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { given, scenario } from "./notifier.ts";

const arranged = given({ start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [external(todo)] });

export const receiveAdded = scenario({
  description: "Receive an added task; no violation",
  given: arranged,
  when: (w) => {
    w.net.deliver(w.peer.todo.emit(todo.taskAdded, { taskId: "task-1", title: "Buy milk" }, { resultOf: null }));
  },
  then: () => [],
});

export const receiveAddedEmptyTitle = scenario({
  description:
    "Receive an added task with an empty title; the payload schema of taskAdded rejects it, so test reports eventPayloadSchema",
  given: arranged,
  when: (w) => {
    w.net.deliver(w.peer.todo.emit(todo.taskAdded, { taskId: "task-1", title: "" }, { resultOf: null }));
  },
  then: () => [],
});

const withNote = { taskId: "task-1", title: "Buy milk", note: "two bottles" };

export const receiveAddedWithUnknownField = scenario({
  description:
    "Receive an added task with a field that taskAdded does not have; a field that nothing reads is the sender's mistake, so test reports eventPayloadSchema",
  given: arranged,
  when: (w) => {
    w.net.deliver(w.peer.todo.emit(todo.taskAdded, withNote, { resultOf: null }));
  },
  then: () => [],
});
