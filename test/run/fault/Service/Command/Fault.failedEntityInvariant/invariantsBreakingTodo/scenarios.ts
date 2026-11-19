import { addTask, scenario } from "./todo.ts";

export const addBlank = scenario({
  description:
    "Add a task with a blank title; without requires, the task fails the invariant titleNotBlank of Task, so test reports failedEntityInvariant",
  given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [], Tally: { added: 0 } }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: " " });
  },
  then: () => [],
});
