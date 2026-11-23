import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario } from "./backlog.ts";

export const work = scenario({
  description:
    "Add one task and nothing else. The task that taskAdded names always exists, so completeChores never binds added to null; its title does not start with Chore, so the guard chore is never true; no second task has the title, so completeDuplicates never binds earlier to a value; and no trace sends completeTask. verify --coverage reports automationBindingNull, automationGuard, automationBindingValue, and request",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
  },
  then: () => [],
});
