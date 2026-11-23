import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario } from "./todo.ts";

export const addTwo = scenario({
  description: "Add two tasks; without requires, the second makes Tally fail its invariant belowTwo",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [], Tally: { added: 0 } }, peers: [] },
  when: (w) => {
    w.client.as("client").send(addTask, { taskId: "task-1", title: "Buy milk" });
    w.client.as("client").send(addTask, { taskId: "task-2", title: "Buy eggs" });
  },
  then: () => [],
});
