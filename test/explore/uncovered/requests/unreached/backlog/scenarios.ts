import { addTask, scenario } from "./backlog.ts";

export const work = scenario({
  description:
    "Add one task and nothing else; the paths that test appends never call taskTitles with an empty prefix, and the ref check rejects an unknown taskId before renameTask binds the task, so test reports requiresRejection and bindsRejection. No title or prefix that the paths try starts with Chore, so renameTask is never accepted and taskTitles is never fulfilled, and test reports successAnswer for both. No scenario runs archive, so test reports only request for archiveTask and archivedTitles. Nothing sends showNotification of device, so test reports request for it",
  given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
  },
  then: () => [],
});
