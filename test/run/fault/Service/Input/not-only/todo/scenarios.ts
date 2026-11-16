import { addTask, scenario, taskNamed } from "./todo.ts";

export const askShared = scenario(
  "Add two tasks with one title and ask for the task of that title; only() finds two, so test reports notOnly",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: {} },
    when: (w) => {
      w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
      w.client.send(addTask, { taskId: "task-2", title: "Buy milk" });
      w.client.call(taskNamed, { title: "Buy milk" });
    },
    then: () => [],
  },
);
