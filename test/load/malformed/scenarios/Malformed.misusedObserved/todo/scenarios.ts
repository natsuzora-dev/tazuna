import { addTask, scenario, taskCount } from "./todo.ts";

export const convertsObserved = scenario({
  description:
    "Write the count that a query line observes into a title as a string; check reports misusedObserved for the line",
  given: { start: "2026-10-25T10:00:00+09:00", records: { Task: [] }, peers: [] },
  when: (w) => {
    const counting = w.client.call(taskCount, {});
    w.client.send(addTask, { taskId: "task-1", title: String(counting.output.count) });
  },
  then: () => [],
});
