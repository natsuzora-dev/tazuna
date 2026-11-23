import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, completeTask, scenario, taskTitles } from "./todo.ts";

export const answersWrongResults = scenario({
  description:
    "Add a task twice, complete a missing task, list the titles, complete the task, and add another task; the implementation trace rejects the completeTask of the missing task as requires, which the spec rejects as not-found",
  given: { start: parseInstant("2026-10-25T00:00:00Z"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.as("client").send(addTask, { taskId: "task-1", title: "Buy milk" });
    w.client.as("client").send(addTask, { taskId: "task-1", title: "Buy eggs" });
    w.client.as("client").send(completeTask, { taskId: "task-9" });
    w.client.as("client").call(taskTitles, {});
    w.client.as("client").send(completeTask, { taskId: "task-1" });
    w.client.as("client").send(addTask, { taskId: "task-2", title: "Buy eggs" });
  },
  then: () => [],
});
