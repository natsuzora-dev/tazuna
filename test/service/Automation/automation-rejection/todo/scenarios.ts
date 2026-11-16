import { at, mock, scenario, send } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { addTask, notifyAdded } from "./todo.ts";

export const notifiedAfterAdd = scenario(
  "Add a task and accept the notification; notifyAdded reacts to taskAdded, sends device.showNotification as a request, and receives the mock's acceptance",
  [
    at("2026-10-25T10:00:00+09:00"),
    send(addTask, { taskId: "task-1", title: "Buy milk" }),
    mock(notifyAdded, [device.showNotification, { result: "accepted" }]),
  ],
);

export const ignoredUnavailable = scenario(
  "Add a task and reject the notification with unavailable; notifyAdded ignores the rejection by onRejected: [], so no violation is reported",
  [
    at("2026-10-25T10:00:00+09:00"),
    send(addTask, { taskId: "task-1", title: "Buy milk" }),
    mock(notifyAdded, [device.showNotification, { result: "rejected", rejection: { kind: "unavailable" } }]),
  ],
);
