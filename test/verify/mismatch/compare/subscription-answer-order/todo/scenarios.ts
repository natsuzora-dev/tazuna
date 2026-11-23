import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, hasTasks, scenario, taskCount, taskIds } from "./todo.ts";

export const subscribed = scenario({
  description:
    "Subscribe three times, add a task, unsubscribe from taskIds, and add another task; a subscription answer has no order with the other outputs of its message, so verify treats as matching an implementation trace that sends the subscription answers before the answer and events of addTask; no violation",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => {
    const ids = w.client.as("client").subscribe(taskIds, {});
    w.client.as("client").subscribe(taskCount, {});
    w.client.as("client").subscribe(hasTasks, {});
    w.client.as("client").send(addTask, { taskId: "task-1" });
    w.client.unsubscribe(ids);
    w.client.as("client").send(addTask, { taskId: "task-2" });
  },
  then: () => [],
});
