import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, remind, scenario } from "./backlog.ts";

export const work = scenario({
  description:
    "Add a task whose title does not start with Chore, and remind it; addTask never emits choreAdded, so verify --coverage reports automation for remindChores and remindOpenChores, and nothing about the binding chore or the guard open of remindOpenChores",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
    w.client.send(remind, { taskId: "task-1" });
  },
  then: () => [],
});
