import { at, scenario, send, subscribe, unsubscribe } from "@natsuzora-dev/tazuna";
import { addTask, hasTasks, taskCount, taskIds } from "./todo.ts";

export const subscribed = scenario(
  "Subscribe three times, add a task, unsubscribe s1, and add another task; a subscription answer has no order with the other outputs of its message, so verify treats as matching an implementation trace that sends the subscription answers before the answer and events of addTask; no violation",
  [
    at("2026-10-25T09:00:00+09:00"),
    subscribe(taskIds, {}, { id: "s1" }),
    subscribe(taskCount, {}, { id: "s2" }),
    subscribe(hasTasks, {}, { id: "s3" }),
    send(addTask, { taskId: "task-1" }),
    unsubscribe("s1"),
    send(addTask, { taskId: "task-2" }),
  ],
);
