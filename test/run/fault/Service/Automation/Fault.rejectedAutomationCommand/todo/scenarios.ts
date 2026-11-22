import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario } from "./todo.ts";

export const addLong = scenario({
  description:
    "Add a task with a long title; the guard short of countAddedTask keeps it from sending countAdded; no violation",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [], Stats: { added: 0 } }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk and bread" });
  },
  then: () => [],
});
