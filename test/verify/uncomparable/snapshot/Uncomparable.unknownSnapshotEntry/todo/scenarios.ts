import { addTask, scenario } from "./todo.ts";

export const addOne = scenario({
  description: "Add a task; the run matches the snapshot; no violation",
  given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
  },
  then: () => [],
});
