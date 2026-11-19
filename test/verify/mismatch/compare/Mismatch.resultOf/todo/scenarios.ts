import { addTask, scenario } from "./todo.ts";

export const addThreeWrongEvents = scenario({
  description:
    "Add three tasks; the implementation trace names the second addTask as the result of the second taskAdded, which the spec emits as no result",
  given: { start: "2026-10-25T00:00:00Z", records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
    w.client.send(addTask, { taskId: "task-2", title: "Buy eggs" });
    w.client.send(addTask, { taskId: "task-1", title: "Buy tea" });
  },
  then: () => [],
});
