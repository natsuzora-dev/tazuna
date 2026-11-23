import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, completeTask, scenario } from "./backlog.ts";

export const work = scenario({
  description:
    "Add a task whose title does not start with Chore, complete it twice, and complete a missing task; the guard chore is never true",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.as("client").send(addTask, { taskId: "task-1", title: "Buy milk" });
    w.client.as("client").send(completeTask, { taskId: "task-1" });
    w.client.as("client").send(completeTask, { taskId: "task-1" });
    w.client.as("client").send(completeTask, { taskId: "task-9" });
  },
  then: () => [],
});
