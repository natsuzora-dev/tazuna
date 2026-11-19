import { addTask, scenario } from "./backlog.ts";

export const work = scenario({
  description:
    "Add one task; the ref check rejects an unknown taskId before renameTask binds the task, so binding it never rejects",
  given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
  },
  then: () => [],
});
