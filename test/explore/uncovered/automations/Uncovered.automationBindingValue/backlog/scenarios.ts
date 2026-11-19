import { addTask, scenario } from "./backlog.ts";

export const work = scenario({
  description:
    "Add one task; the paths of test add no second task with the title, so completeDuplicates never binds earlier to a value",
  given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
  },
  then: () => [],
});
