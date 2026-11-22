import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario } from "./todo.ts";

export const addTwice = scenario({
  description:
    "Add two tasks; countAdded reacts after taskAdded is applied to the records, so it reports 1 after the first addTask and 2 after the second",
  given: { start: parseInstant("2026-10-25T10:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1" });
    w.client.send(addTask, { taskId: "task-2" });
  },
  then: () => [],
});
