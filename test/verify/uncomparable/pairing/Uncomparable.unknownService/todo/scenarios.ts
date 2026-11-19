import { addTask, scenario } from "./todo.ts";

export const addOne = scenario({
  description:
    "Add a task; traces/todo/addOne.jsonl pairs with this snapshot, while traces/other/addOne.jsonl names no service of the spec, so verify reports unknownService",
  given: { start: "2026-10-25T00:00:00Z", records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
  },
  then: () => [],
});
