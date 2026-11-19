import { taskCard, taskNote } from "./queries.ts";
import { addTask, completeTask, scenario } from "./todo.ts";

export const completeTwice = scenario({
  description:
    "Add a task, complete it twice, and ask for taskNote with an empty taskId; todo rejects the second completeTask and taskNote with requires. The implementation trace differs from the snapshot in ids, time format, rejection reasons, and fields outside the schema, and lacks the event lines outside the contract, and verify treats it as matching; no violation",
  given: { start: "2026-10-25T10:00:00+09:00", records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1" });
    w.client.send(completeTask, { taskId: "task-1" });
    w.client.send(completeTask, { taskId: "task-1" });
    w.client.call(taskNote, { taskId: "" });
  },
  then: () => [],
});

export const showCard = scenario({
  description:
    "Ask for the task card; verify reads values with the schema of the definition that each trace line names, so it treats the implementation's taskCard answer as matching the snapshot. The answer has fields outside the schema at every depth, including inside z.strictObject and inside the options of z.union and z.discriminatedUnion, writes datetime values with +09:00, and orders object fields differently; no violation",
  given: { start: "2026-10-25T10:00:00+09:00", records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.call(taskCard, {});
  },
  then: () => [],
});
