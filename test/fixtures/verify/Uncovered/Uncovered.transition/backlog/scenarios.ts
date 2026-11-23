import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario } from "./backlog.ts";

export const work = scenario({
  description: "Add one task; no trace adds a second task while progress is busy, so its transition is never taken",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.as("client").send(addTask, { taskId: "task-1", title: "Buy milk" });
  },
  then: () => [],
});
