import { addTask, completeTask, scenario, taskTitles } from "./todo.ts";

export const answersWrongResults = scenario({
  description:
    "Add a task twice, complete a missing task, list the titles, complete the task, and add another task; the implementation trace has no answer to the second completeTask",
  given: { start: "2026-10-25T00:00:00Z", records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
    w.client.send(addTask, { taskId: "task-1", title: "Buy eggs" });
    w.client.send(completeTask, { taskId: "task-9" });
    w.client.call(taskTitles, {});
    w.client.send(completeTask, { taskId: "task-1" });
    w.client.send(addTask, { taskId: "task-2", title: "Buy eggs" });
  },
  then: () => [],
});
