import { addTask, scenario } from "./todo.ts";

export const addTwoWithOneTag = scenario({
  description: "Add two tasks with one tag; test reports duplicateItemKey",
  given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", tag: "home" });
    w.client.send(addTask, { taskId: "task-2", tag: "home" });
  },
  then: () => [],
});
