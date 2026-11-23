import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario } from "./todo.ts";

export const addBlank = scenario({
  description:
    "Add a task with a blank title; without requires, the task fails the invariant titleNotBlank of Task, so test reports failedEntityInvariant. The id domain holds only task-1 so that the paths add no second task, which would also break belowTwo and uniqueTitles, as the example invariants shows",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [], Tally: { added: 0 } }, peers: [] },
  when: (w) => {
    w.client.as("client").send(addTask, { taskId: "task-1", title: "" });
  },
  then: () => [],
});
