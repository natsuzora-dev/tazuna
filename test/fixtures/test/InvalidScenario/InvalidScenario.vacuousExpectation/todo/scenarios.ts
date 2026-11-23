import { emitted, parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario } from "./todo.ts";

export const addMilk = scenario({
  description:
    "Add a task, and state the events that todo emits, which its contract lists none of, so the expectation cannot fail",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => {
    return { add: w.client.as("client").send(addTask, { taskId: "task-1", title: "Buy milk" }) };
  },
  then: ({ add }) => [emitted(add, [])],
});
