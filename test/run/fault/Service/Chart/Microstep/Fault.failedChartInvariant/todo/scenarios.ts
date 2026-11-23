import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario } from "./todo.ts";

export const addTwo = scenario({
  description: "Add two tasks; the guard first keeps counter from counting the second; no violation",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
    w.client.send(addTask, { taskId: "task-2", title: "Buy eggs" });
  },
  then: () => [],
});
