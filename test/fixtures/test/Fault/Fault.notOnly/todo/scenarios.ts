import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario, taskNamed } from "./todo.ts";

export const askShared = scenario({
  description:
    "Add two tasks with one title and ask for the task of that title; only() finds two, so test reports notOnly",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.as("client").send(addTask, { taskId: "task-1", title: "Buy milk" });
    w.client.as("client").send(addTask, { taskId: "task-2", title: "Buy milk" });
    w.client.as("client").call(taskNamed, { title: "Buy milk" });
  },
  then: () => [],
});
