import { addTask, scenario } from "./todo.ts";

export const addUntitled = scenario({
  description:
    "Add a task without a title; the guard titled of countTitledTask throws, so test reports exception of countTitledTask",
  given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [], Stats: { added: 0 } }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "" });
  },
  then: () => [],
});
