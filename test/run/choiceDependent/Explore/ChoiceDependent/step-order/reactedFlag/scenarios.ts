import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTasks, scenario } from "./reactedFlag.ts";

export const addTwo = scenario({
  description:
    "Add two tasks in one group; setOnAdd sends set for each, the two sets differ only by input, and the one taken last decides the flag, so test reports stepOrder",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Flag: { by: "" } }, peers: [] },
  when: (w) => {
    w.client.as("client").send(addTasks, { taskIds: ["task-1", "task-2"] });
  },
  then: () => [],
});
