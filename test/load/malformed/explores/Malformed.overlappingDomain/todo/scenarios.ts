import { addTask, given, scenario } from "./todo.ts";

export const added = scenario({
  description: "Add a task",
  given: given({ start: "2026-10-25T10:00:00+09:00", records: { Task: [] }, peers: [] }),
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
  },
  then: () => [],
});
