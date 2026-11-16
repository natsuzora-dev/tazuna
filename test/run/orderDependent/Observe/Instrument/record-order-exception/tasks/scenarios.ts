import { at, call, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask, subtaskCounts } from "./tasks.ts";

export const addTaskAndSubtask = scenario(
  "Add a task and its subtask and count the subtasks; the count reads each parent before its subtasks and throws when the Bag visits the records in reverse order, so test reports reversedException",
  [
    at("2026-10-25T09:00:00+09:00"),
    send(addTask, { taskId: "task-1", parentId: null }),
    send(addTask, { taskId: "task-2", parentId: "task-1" }),
    call(subtaskCounts, {}),
  ],
);
