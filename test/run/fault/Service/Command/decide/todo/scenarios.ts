import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario } from "./todo.ts";

export const addUntitled = scenario({
  description: "Add a task without a title; decide of addTask throws, so test reports exception of addTask",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "" });
  },
  then: () => [],
});
