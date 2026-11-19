import { addTask, scenario, subtaskCounts } from "./tasks.ts";

export const addTaskAndSubtask = scenario({
  description:
    "Add a task and its subtask and count the subtasks; the count reads each parent before its subtasks and throws when the Bag visits the records in reverse order, so test reports reversedException",
  given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", parentId: null });
    w.client.send(addTask, { taskId: "task-2", parentId: "task-1" });
    w.client.call(subtaskCounts, {});
  },
  then: () => [],
});
