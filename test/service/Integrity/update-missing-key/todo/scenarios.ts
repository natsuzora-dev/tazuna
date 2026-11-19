import { renameTask, scenario, taskCount } from "./todo.ts";

export const renameMissing = scenario({
  description:
    "Rename task-1, which nobody added, and count the tasks; Task has no invariants, so renameTask rewrites task-1 with taskRenamed, which creates task-1 with only id and title, and taskCount returns 1",
  given: { start: "2026-10-25T10:00:00+09:00", records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(renameTask, { taskId: "task-1", title: "Buy milk" });
    w.client.call(taskCount, {});
  },
  then: () => [],
});
