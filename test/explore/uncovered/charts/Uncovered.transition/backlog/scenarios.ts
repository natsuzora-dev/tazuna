import { addTask, scenario } from "./backlog.ts";

export const work = scenario({
  description:
    "Add one task; the id domain holds only its id, so the paths of test add no second task while progress is busy, and its transition is never taken",
  given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
  },
  then: () => [],
});
