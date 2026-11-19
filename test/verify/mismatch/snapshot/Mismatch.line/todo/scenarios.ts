import { addTask, scenario } from "./todo.ts";

export const addOneEdited = scenario({
  description:
    "Add a task; the snapshot has a blank line 2, so test reports its taskAdded line, which says Buy eggs, at line 4",
  given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
  },
  then: () => [],
});
