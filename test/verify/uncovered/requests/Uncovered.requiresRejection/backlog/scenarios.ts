import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario, taskTitles } from "./backlog.ts";

export const work = scenario({
  description:
    "Add a task and list the titles that start with Buy; no trace calls taskTitles with an empty prefix, so notEmpty never rejects",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
    w.client.call(taskTitles, { prefix: "Buy" });
  },
  then: () => [],
});
