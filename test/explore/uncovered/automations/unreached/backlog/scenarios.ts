import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario } from "./backlog.ts";

export const work = scenario({
  description:
    "Add one task and nothing else. The task that taskAdded names always exists, so completeChores never binds added to null; no title that the paths of test add starts with Chore, so the guard chore is never true; and the id domain holds only its id, so the paths add no second task, completeDuplicates never binds earlier to a value, and completeTask always finds the task. test reports automationBindingNull, automationGuard, automationBindingValue, and bindsRejection",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
  },
  then: () => [],
});
