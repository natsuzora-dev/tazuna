import { addTask, scenario } from "./todo.ts";

export const addOne = scenario({
  description:
    "Add a task; copyAdded calls createKey with a string instead of ref() of an entity, past the types without a written any, so test reports exception of copyAdded",
  given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
  },
  then: () => [],
});
