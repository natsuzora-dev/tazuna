import { at, scenario, send, subscribe, unsubscribe } from "@natsuzora-dev/tazuna";
import { addTask, hasTasks, taskCount, taskIds } from "./todo.ts";

export const subscribed = scenario(
  "Subscribe three times, add a task, unsubscribe s1, and add another task; each time todo finishes processing addTask, it sends one answer line for each subscription whose answer changed. It sends no answer to the subscription s3 to hasTasks, whose answer does not change, or to the ended subscription s1 to taskIds",
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
