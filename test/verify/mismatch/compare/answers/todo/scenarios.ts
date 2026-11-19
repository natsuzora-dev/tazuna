import { addTask, completeTask, scenario, taskCard, taskTitles } from "./todo.ts";

export const answers = scenario({
  description: "Add a task twice, complete a missing task, list the titles, and complete the task; no violation",
  given: { start: "2026-10-25T00:00:00Z", records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
    w.client.send(addTask, { taskId: "task-1", title: "Buy eggs" });
    w.client.send(completeTask, { taskId: "task-9" });
    w.client.call(taskTitles, {});
    w.client.send(completeTask, { taskId: "task-1" });
  },
  then: () => [],
});

export const answersWrongResults = scenario({
  description:
    "Add a task twice, complete a missing task, list the titles, complete the task, and add another task; the implementation trace of this scenario answers with other results, rejection kinds, and outputs, so verify reports Mismatch.result, Mismatch.rejection, Mismatch.output, missingAnswer, and unexpectedLine",
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

export const showCards = scenario({
  description:
    "Ask for the task card three times; the implementation trace of this scenario answers with an unknown field, another part name, and another time, so verify reports Mismatch.output",
  given: { start: "2026-10-25T00:00:00Z", records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.call(taskCard, {});
    w.client.call(taskCard, {});
    w.client.call(taskCard, {});
  },
  then: () => [],
});
