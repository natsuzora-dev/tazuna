import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario } from "./todo.ts";

export const addThree = scenario({
  description: "Add two tasks and a task with the first id; no violation",
  given: { start: parseInstant("2026-10-25T00:00:00Z"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
    w.client.send(addTask, { taskId: "task-2", title: "Buy eggs" });
    w.client.send(addTask, { taskId: "task-1", title: "Buy tea" });
  },
  then: () => [],
});

export const addThreeWrongEvents = scenario({
  description:
    "Same inputs as addThree; the implementation trace of this scenario emits taskAdded with another title, emits the second taskAdded without the resultOf that the spec gives it, and emits an extra one, so verify reports Mismatch.event, Mismatch.resultOf, and unexpectedLine",
  given: { start: parseInstant("2026-10-25T00:00:00Z"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
    w.client.send(addTask, { taskId: "task-2", title: "Buy eggs" });
    w.client.send(addTask, { taskId: "task-1", title: "Buy tea" });
  },
  then: () => [],
});
