import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, completeTask, scenario } from "./backlog.ts";

export const work = scenario({
  description:
    "Add a task, which completeAdded completes, then complete a missing task and the done one; completeAdded's binding added always finds the task that taskAdded names, so verify --coverage reports automationBindingNull",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
    w.client.send(completeTask, { taskId: "task-9" });
    w.client.send(completeTask, { taskId: "task-1" });
  },
  then: () => [],
});
