import { addTask, deleteTask, pinTask, scenario } from "./todo.ts";

export const deletePinned = scenario({
  description:
    "Delete the pinned task by deleteTask; Pin keeps referring to the deleted task, so test reports danglingSingleRef",
  given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [], Comment: [], Pin: { taskId: null } }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
    w.client.send(pinTask, { taskId: "task-1" });
    w.client.send(deleteTask, { taskId: "task-1" });
  },
  then: () => [],
});
