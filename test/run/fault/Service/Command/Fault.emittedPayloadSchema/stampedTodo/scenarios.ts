import { addTask, scenario } from "./todo.ts";

export const addOne = scenario({
  description:
    "Add a task; addTask emits taskAdded with the text of an Instant, which the payload schema does not encode, so test reports emittedPayloadSchema in Lean too, which once parsed the text",
  given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1" });
  },
  then: () => [],
});
