import { addTask, scenario } from "./todo.ts";

export const addOne = scenario(
  "Add a task; addTask decides taskRemoved, whose payload matches taskAdded's but which its emits do not list, so test reports unlistedEmittedEvent",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [] },
    when: (w) => {
      w.client.send(addTask, { taskId: "task-1" });
    },
    then: () => [],
  },
);
