import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario } from "./todo.ts";

export const separateValues = scenario({
  description:
    "Add two tasks; in the one microstep of taskAdded, the transition of counting reads and writes only count and the transition of remembering only lastTaskId, so tracker reports no pair of the two transitions. The input of the sends of reporting is evaluated after the microstep, so reading the count that counting writes makes no pair",
  given: { start: parseInstant("2026-10-25T10:00:00+09:00"), records: {}, peers: [] },
  when: (w) => {
    w.client.as("client").send(addTask, { taskId: "task-1" });
    w.client.as("client").send(addTask, { taskId: "task-2" });
  },
  then: () => [],
});
