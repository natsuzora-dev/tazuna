import { addTask, scenario } from "./todo.ts";

export const addOne = scenario(
  "Add a task; addTask emits taskAdded with an empty title, which the payload schema rejects, so test reports emittedPayloadSchema",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: {} },
    when: (w) => {
      w.client.send(addTask, { taskId: "task-1" });
    },
    then: () => [],
  },
);
