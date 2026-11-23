import { parseInstant } from "@natsuzora-dev/tazuna";
import { taskCard, taskNote } from "./queries.ts";
import { addTask, completeTask, scenario } from "./todo.ts";

export const completeTwice = scenario({
  description:
    "Add a task, complete it twice, and ask for taskNote with an empty taskId; todo rejects the second completeTask and taskNote with requires. The implementation trace differs from the spec's lines in ids, time format, and rejection reasons, and lacks the event lines outside the contract, and verify treats it as matching; no violation",
  given: { start: parseInstant("2026-10-25T10:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.as("client").send(addTask, { taskId: "task-1" });
    w.client.as("client").send(completeTask, { taskId: "task-1" });
    w.client.as("client").send(completeTask, { taskId: "task-1" });
    w.client.as("client").call(taskNote, { taskId: "" });
  },
  then: () => [],
});

export const showCard = scenario({
  description:
    "Ask for the task card; verify reads values with the schema of the definition that each trace line names, so it treats the implementation's taskCard answer as matching the spec's. The answer writes instant values with +09:00 and orders object fields differently, inside the options of z.union and z.discriminatedUnion too; no violation",
  given: { start: parseInstant("2026-10-25T10:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.as("client").call(taskCard, {});
  },
  then: () => [],
});
