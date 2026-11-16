import { run } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { scenario } from "./notifier.ts";

export const redelivered = scenario(
  "Receive todo.taskAdded twice with the same id; notifier does not process the second",
  {
    given: {
      start: "2026-10-25T09:00:00+09:00",
      records: { OpenTask: [] },
      peers: { todo: run(todo, { Task: [] }) },
    },
    when: (w) => {
      const add = w.client.send(todo.addTask, { taskId: "task-1", title: "Buy milk" });
      const added = w.peer.todo.emit(todo.taskAdded, { taskId: "task-1" }, { resultOf: add });
      w.net.redeliver(added);
    },
    then: () => [],
  },
);
