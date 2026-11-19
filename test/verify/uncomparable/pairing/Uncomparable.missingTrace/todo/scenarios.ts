import { addTask, scenario } from "./todo.ts";

export const addOne = scenario({
  description: "Add a task; its snapshot and trace pair up; no violation",
  given: { start: "2026-10-25T00:00:00Z", records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
  },
  then: () => [],
});

export const addTwo = scenario({
  description: "Add two tasks; its snapshot has no trace, so verify reports missingTrace",
  given: { start: "2026-10-25T00:00:00Z", records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
    w.client.send(addTask, { taskId: "task-2", title: "Buy eggs" });
  },
  then: () => [],
});
