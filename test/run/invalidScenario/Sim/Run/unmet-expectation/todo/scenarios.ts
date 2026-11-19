import { answered, rejected } from "@natsuzora-dev/tazuna";
import { addTask, scenario } from "./todo.ts";

export const addMilk = scenario({
  description: "Add a task, and state that todo rejects it, though todo accepts it",
  given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: [] },
  when: (w) => ({ add: w.client.send(addTask, { taskId: "task-1", title: "Buy milk" }) }),
  then: ({ add }) => [answered(add, rejected("already-exists"))],
});
