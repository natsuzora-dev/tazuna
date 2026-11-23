import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario } from "./todo.ts";

export const addOneUnsnapshotted = scenario({
  description: "Add a task; the scenario has no snapshot, so test reports missingSnapshot",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.as("client").send(addTask, { taskId: "task-1", title: "Buy milk" });
  },
  then: () => [],
});
