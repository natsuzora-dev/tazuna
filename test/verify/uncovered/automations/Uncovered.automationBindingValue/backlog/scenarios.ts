import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, completeTask, scenario } from "./backlog.ts";

export const work = scenario({
  description:
    "Add one task and complete it; no second task has the title, so completeDuplicates never binds earlier to a value",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.as("client").send(addTask, { taskId: "task-1", title: "Buy milk" });
    w.client.as("client").send(completeTask, { taskId: "task-1" });
  },
  then: () => [],
});
