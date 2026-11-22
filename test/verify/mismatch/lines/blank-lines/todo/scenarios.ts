import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario } from "./todo.ts";

export const addOneEdited = scenario({
  description: "Add a task; the trace has a blank line 2, so verify reports its answer, a rejection, at line 3",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
  },
  then: () => [],
});

export const addOneUnanswered = scenario({
  description:
    "Add a task; the snapshot has a blank line 2, so verify reports the answer that the trace lacks at snapshot line 3",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
  },
  then: () => [],
});
