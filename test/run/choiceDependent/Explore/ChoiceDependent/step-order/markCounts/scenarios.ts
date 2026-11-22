import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario } from "./markCounts.ts";

export const addOne = scenario({
  description:
    "Add a task; markB counts the marks, and markA adds one, so the count depends on which of the two the queue takes first, and test reports stepOrder",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Mark: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1" });
  },
  then: () => [],
});
