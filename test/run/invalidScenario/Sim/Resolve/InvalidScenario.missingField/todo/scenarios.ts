import { addTask, firstNote, scenario } from "./todo.ts";

export const copyMissingNote = scenario({
  description:
    "Ask for the first note while no task has one, and add a task with that note, which the answer has no field for",
  given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: [] },
  when: (w) => {
    const noting = w.client.call(firstNote, {});
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk", note: noting.output.note });
  },
  then: () => [],
});
