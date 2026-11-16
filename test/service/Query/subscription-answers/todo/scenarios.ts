import { at, scenario, send, subscribe, unsubscribe } from "@natsuzora-dev/tazuna";
import { addTask, hasTasks, taskCount, taskIds } from "./todo.ts";

const ids = subscribe(taskIds, {});

export const subscribed = scenario(
  "Subscribe three times, add a task, unsubscribe from taskIds, and add another task; each time todo finishes processing addTask, it sends one answer line for each subscription whose answer changed. It sends no answer to the subscription to hasTasks, whose answer does not change, or to the ended subscription to taskIds",
  [
    at("2026-10-25T09:00:00+09:00"),
    ids,
    subscribe(taskCount, {}),
    subscribe(hasTasks, {}),
    send(addTask, { taskId: "task-1" }),
    unsubscribe(ids),
    send(addTask, { taskId: "task-2" }),
  ],
);
