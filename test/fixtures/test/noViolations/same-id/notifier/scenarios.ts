import { parseInstant, run } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { scenario } from "./notifier.ts";

export const redelivered = scenario({
  description: "Receive todo.taskAdded twice with the same id; notifier does not process the second",
  given: {
    start: parseInstant("2026-10-25T09:00:00+09:00"),
    records: { OpenTask: [] },
    peers: [run(todo, { Task: [] })],
  },
  when: (w) => {
    const add = w.client.as("client").send(todo.addTask, { taskId: "task-1", title: "Buy milk" });
    const added = w.peer.todo.emit(todo.taskAdded, { taskId: "task-1" }, { resultOf: add });
    w.net.deliver(added);
    w.net.redeliver(added);
  },
  then: () => [],
});
