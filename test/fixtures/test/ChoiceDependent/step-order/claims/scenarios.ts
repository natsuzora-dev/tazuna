import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTasks, scenario } from "./claims.ts";

export const addTwo = scenario({
  description:
    "Add task-1 and task-2; the copies of claimer for the two tasks send claim, and the one taken last decides the winner, so test reports stepOrder",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [], Winner: { taskId: "" } }, peers: [] },
  when: (w) => {
    w.client.as("client").send(addTasks, { taskIds: ["task-1", "task-2"] });
  },
  then: () => [],
});
