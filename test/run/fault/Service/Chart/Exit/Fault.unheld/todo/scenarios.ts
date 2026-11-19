import { addTask, scenario } from "./todo.ts";

export const addOne = scenario({
  description:
    "Add a task; firstTaskWatcher reads the held task, while watcher reads latest, which watching does not have, so test reports unheld",
  given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
  },
  then: () => [],
});
