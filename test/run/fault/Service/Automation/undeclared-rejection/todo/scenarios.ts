import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./todo.ts";

export const notificationAwaited = scenario(
  "Add a task and leave the device's answer to the notification open; showNotification declares no rejection kinds, so test appends no rejected answer and reports nothing",
  [at("2026-10-25T09:00:00+09:00"), send(addTask, { taskId: "task-1", title: "Buy milk" })],
);
