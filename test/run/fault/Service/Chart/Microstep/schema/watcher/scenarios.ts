import { addTask, scenario } from "./watcher.ts";

export const addOne = scenario({
  description: "Add one task; watcher enters watching with that task; no violation",
  given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
  },
  then: () => [],
});
