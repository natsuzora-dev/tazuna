import { run } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { announce, scenario } from "./notifier.ts";

export const announcesAdded = scenario(
  "Receive taskAdded for the task that the client adds to todo; todo's run has a snapshot but no trace, so verify reports missingTrace",
  {
    given: { start: "2026-10-25T10:00:00+09:00", records: {}, peers: { todo: run(todo, { Task: [] }) } },
    when: (w) => {
      const add = w.client.send(todo.addTask, { taskId: "task-1", title: "Buy milk" });
      w.net.deliver(w.peer.todo.emit(todo.taskAdded, { taskId: "task-1" }, { resultOf: add }));
    },
    then: () => [],
  },
);

export const announcesDirectly = scenario(
  "Announce without todo; no todo run has a snapshot, so verify skips the trace announcesDirectly.todo.jsonl, and reports announcesDirectly.notifier.jsonl, which names no other service's run, as unknownScenario",
  {
    given: { start: "2026-10-25T10:00:00+09:00", records: {}, peers: { todo: run(todo, { Task: [] }) } },
    when: (w) => {
      w.client.send(announce, { taskId: "task-1" });
    },
    then: () => [],
  },
);
