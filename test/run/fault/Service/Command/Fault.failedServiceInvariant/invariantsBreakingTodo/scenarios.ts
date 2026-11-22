import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario } from "./todo.ts";

export const addSameTitle = scenario({
  description:
    "Add two tasks with the same title; without requires, the tasks fail the invariant uniqueTitles of the service",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [], Tally: { added: 0 } }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
    w.client.send(addTask, { taskId: "task-2", title: "Buy milk" });
  },
  then: () => [],
});
