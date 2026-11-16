import { addTask, scenario } from "./todo.ts";

export const addUntitled = scenario(
  "Add a task without a title; the invariant titled of Task throws, so test reports exception of Task",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: {} },
    when: (w) => {
      w.client.send(addTask, { taskId: "task-1", title: "" });
    },
    then: () => [],
  },
);
