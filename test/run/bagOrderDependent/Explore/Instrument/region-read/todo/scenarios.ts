import { addTask, scenario } from "./todo.ts";

export const addOne = scenario({
  description: "Add a task; test reports assignRead",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1" });
  },
  then: () => [],
});
