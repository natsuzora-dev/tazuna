import { addTask, scenario } from "./cleanup.ts";

export const addOne = scenario(
  "Add a task: markDone writes the done field of the task, and dropTask deletes the task, so in either order the task is gone, and only taskDone, which no contract lists, differs; no violation",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: {} },
    when: (w) => {
      w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
    },
    then: () => [],
  },
);
