import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario } from "./todo.ts";

export const addTwo = scenario({
  description:
    "Add two tasks; counter counts two, which fails its invariant atMostOne, so test reports failedChartInvariant",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.as("client").send(addTask, { taskId: "task-1", title: "Buy milk" });
    w.client.as("client").send(addTask, { taskId: "task-2", title: "Buy eggs" });
  },
  then: () => [],
});
