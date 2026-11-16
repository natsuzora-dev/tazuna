import { run } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { scenario } from "./notifier.ts";

export const announcesAdded = scenario(
  "Receive taskAdded for the task that the client adds to todo; todo's trace of its run emits taskAdded for another task, so verify reports a Mismatch in it",
  {
    given: { start: "2026-10-25T10:00:00+09:00", records: {}, peers: { todo: run(todo, { Task: [] }) } },
    when: (w) => {
      const add = w.client.send(todo.addTask, { taskId: "task-1", title: "Buy milk" });
      w.net.deliver(w.peer.todo.emit(todo.taskAdded, { taskId: "task-1" }, { resultOf: add }));
    },
    then: () => [],
  },
);
