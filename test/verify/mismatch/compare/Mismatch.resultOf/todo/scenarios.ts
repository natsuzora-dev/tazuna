import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario } from "./todo.ts";

export const addThreeWrongEvents = scenario({
  description:
    "Add three tasks; the implementation trace emits the second taskAdded without naming the second addTask as its result, as the spec does",
  given: { start: parseInstant("2026-10-25T00:00:00Z"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.as("client").send(addTask, { taskId: "task-1", title: "Buy milk" });
    w.client.as("client").send(addTask, { taskId: "task-2", title: "Buy eggs" });
    w.client.as("client").send(addTask, { taskId: "task-1", title: "Buy tea" });
  },
  then: () => [],
});
