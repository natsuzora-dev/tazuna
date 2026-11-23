import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario } from "./todo.ts";

export const syncedWithinMessage = scenario({
  description:
    "Add two tasks; after the transition on taskAdded, added and shown differ, so tally fails its invariant inSync after that microstep and test reports failedChartInvariant, although an always transition in the same message brings shown in line",
  given: { start: parseInstant("2026-10-25T10:00:00+09:00"), records: {}, peers: [] },
  when: (w) => {
    w.client.as("client").send(addTask, { taskId: "task-1" });
    w.client.as("client").send(addTask, { taskId: "task-2" });
  },
  then: () => [],
});
