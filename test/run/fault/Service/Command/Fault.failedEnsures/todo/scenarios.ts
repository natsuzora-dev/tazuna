import { addTask, scenario } from "./todo.ts";

export const addTwo = scenario({
  description: "Add two tasks; no violation",
  given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "milk" });
    w.client.send(addTask, { taskId: "task-2", title: "eggs" });
  },
  then: () => [],
});
