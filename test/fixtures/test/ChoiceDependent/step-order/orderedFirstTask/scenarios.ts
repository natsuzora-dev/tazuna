import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTasks, scenario } from "./orderedFirstTask.ts";

export const addTwo = scenario({
  description:
    "Add two tasks in two groups; remember receives task-1 first, since a group comes after the group before it, so no violation",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Flag: { by: "" } }, peers: [] },
  when: (w) => {
    w.client.as("client").send(addTasks, { taskIds: ["task-1", "task-2"] });
  },
  then: () => [],
});
