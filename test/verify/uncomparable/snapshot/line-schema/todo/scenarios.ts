import { addTask, scenario } from "./todo.ts";

export const addOneCut = scenario({
  description:
    "Add a task; the snapshot's answer line is cut off, so it is not JSON; test reports lineSchema and compares nothing",
  given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
  },
  then: () => [],
});
