import { addTask, scenario } from "./todo.ts";

export const addBlank = scenario("Add a task with a blank title; the requires titleNotBlank rejects it; no violation", {
  given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: {} },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: " " });
  },
  then: () => [],
});

export const addSameTitle = scenario(
  "Add two tasks with the same title; the requires newTitle rejects the second; no violation",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: {} },
    when: (w) => {
      w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
      w.client.send(addTask, { taskId: "task-2", title: "Buy milk" });
    },
    then: () => [],
  },
);
