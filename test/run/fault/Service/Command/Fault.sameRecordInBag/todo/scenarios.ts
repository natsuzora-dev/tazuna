import { addTask, archiveTitle, scenario } from "./todo.ts";

export const archiveShared = scenario({
  description:
    "Archive a title that two tasks share; decide archives the title once per task in one Bag, so test reports sameRecordInBag",
  given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [], Archive: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
    w.client.send(addTask, { taskId: "task-2", title: "Buy milk" });
    w.client.send(archiveTitle, { title: "Buy milk" });
  },
  then: () => [],
});
