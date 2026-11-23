import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario, taskCount } from "./todo.ts";

export const addTwo = scenario({
  description: "Add two tasks and count them; no violation",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.as("client").send(addTask, { taskId: "task-1", title: "milk" });
    w.client.as("client").send(addTask, { taskId: "task-2", title: "eggs" });
    w.client.as("client").call(taskCount, {});
  },
  then: () => [],
});
