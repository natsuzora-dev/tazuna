import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, renameTask, scenario } from "./backlog.ts";

export const work = scenario({
  description: "Add a task and rename it to a title that does not start with Chore, so renameTask is never accepted",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
    w.client.send(renameTask, { taskId: "task-1", title: "Buy tea" });
  },
  then: () => [],
});
