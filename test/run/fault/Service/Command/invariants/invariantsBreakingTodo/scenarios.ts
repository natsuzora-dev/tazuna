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

export const addSameTitle = scenario({
  description:
    "Add two tasks with the same title; without requires, the tasks fail the invariants belowTwo of Tally and uniqueTitles of the service, so test reports failedSingleInvariant and failedServiceInvariant",
  given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [], Tally: { added: 0 } }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
    w.client.send(addTask, { taskId: "task-2", title: "Buy milk" });
  },
  then: () => [],
});
