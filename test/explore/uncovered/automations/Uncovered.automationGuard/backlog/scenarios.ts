import { addTask, scenario } from "./backlog.ts";

export const work = scenario({
  description: "Add one task; no title that the paths of test add starts with Chore, so the guard chore is never true",
  given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
  },
  then: () => [],
});
