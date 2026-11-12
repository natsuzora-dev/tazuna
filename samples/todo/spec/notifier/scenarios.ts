import { at, mock, receive, restart, scenario } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { todo } from "../todo/contract.ts";
import { notification } from "./machines.ts";

const added = (n: number) => receive(todo.taskAdded, { taskId: `task-${n}` });

const elevenTasks = Array.from({ length: 11 }, (_, i) => added(i + 1));

const unavailable = mock(notification, [
  device.requestNotificationPermission,
  { result: "rejected", rejection: { kind: "unavailable" } },
]);
const accepted = mock(notification, [device.requestNotificationPermission, { result: "accepted" }]);

const grants = [accepted, receive(device.notificationPermissionGranted, {}, { resultOf: accepted })];

export const warnsWhenTooMany = scenario(
  "Add too many open tasks and let 1 hour pass while they stay too many; notifier warns, and warns again",
  [
    at("2026-10-25T10:00:00+09:00"),
    added(0),
    ...grants,
    ...elevenTasks,
    at("2026-10-25T11:30:00+09:00"),
    receive(todo.taskCompleted, { taskId: "task-0" }),
  ],
);

export const warnsAgainAfterNotificationAnswered = scenario(
  "Add too many open tasks, let device fail to show the warning, and let 1 hour pass; notifier shows the warning again",
  [
    at("2026-10-25T10:00:00+09:00"),
    added(0),
    ...grants,
    ...elevenTasks,
    mock(notification, [device.showNotification, { result: "rejected", rejection: { kind: "unavailable" } }]),
    at("2026-10-25T11:00:00+09:00"),
    mock(notification, [device.showNotification, { result: "accepted" }]),
  ],
);

export const warnsWithoutNotificationWhileAsking = scenario(
  "While requestNotificationPermission waits for its answer, let the user grant permission in the device settings and add too many open tasks; notifier warns but shows no notification",
  [
    at("2026-10-25T10:00:00+09:00"),
    added(0),
    receive(device.notificationPermissionGranted, {}),
    ...elevenTasks,
    accepted,
  ],
);

export const countsReopenedTask = scenario("Complete a task and reopen it; notifier counts the task again", [
  at("2026-10-25T10:00:00+09:00"),
  added(1),
  ...grants,
  ...Array.from({ length: 9 }, (_, i) => added(i + 2)),
  at("2026-10-25T10:01:00+09:00"),
  receive(todo.taskCompleted, { taskId: "task-1" }),
  added(11),
  receive(todo.taskReopened, { taskId: "task-1" }),
]);

export const warnsWithoutNotificationWhenDenied = scenario(
  "Let the user deny permission and add too many open tasks; notifier warns but shows no notification",
  [
    at("2026-10-25T10:00:00+09:00"),
    added(0),
    accepted,
    receive(device.notificationPermissionDenied, {}, { resultOf: accepted }),
    ...elevenTasks,
  ],
);

export const ignoresRedelivery = scenario("Deliver an event with the same event id twice; notifier counts it once", [
  at("2026-10-25T10:00:00+09:00"),
  receive(todo.taskAdded, { taskId: "task-1" }, { id: "e9" }),
  receive(todo.taskAdded, { taskId: "task-1" }, { id: "e9" }),
]);

export const asksPermissionAgain = scenario(
  "Let device fail to request permission, then let the user grant it; notifier requests at most 3 times 1 minute apart, and requests no more after the grant",
  [
    at("2026-10-25T10:00:00+09:00"),
    added(1),
    unavailable,
    at("2026-10-25T10:01:00+09:00"),
    unavailable,
    at("2026-10-25T10:02:00+09:00"),
    unavailable,
    at("2026-10-25T10:03:00+09:00"),
    added(2),
    accepted,
    receive(device.notificationPermissionGranted, {}, { resultOf: accepted }),
    added(3),
  ],
);

export const warnsWithoutNotificationAfterRevoked = scenario(
  "Let the user grant permission and revoke it in the device settings, and add too many open tasks; notifier warns but shows no notification",
  [
    at("2026-10-25T10:00:00+09:00"),
    added(0),
    ...grants,
    receive(device.notificationPermissionDenied, {}),
    ...elevenTasks,
  ],
);

export const stopsAskingWhenGrantedWhileRetrying = scenario(
  "While notifier waits to request permission again, let the user grant it in the device settings; notifier requests no more",
  [
    at("2026-10-25T10:00:00+09:00"),
    added(1),
    unavailable,
    receive(device.notificationPermissionGranted, {}),
    at("2026-10-25T10:01:00+09:00"),
  ],
);

export const warnsAgainOnStart = scenario(
  "Add too many open tasks and restart the server within 1 hour of the warning; notifier warns again",
  [at("2026-10-25T10:00:00+09:00"), added(0), ...grants, ...elevenTasks, at("2026-10-25T10:10:00+09:00"), restart()],
);

export const asksPermissionAgainOnStart = scenario(
  "Restart the server while a task is open and before the user chooses permission; notifier requests permission again",
  [
    at("2026-10-25T10:00:00+09:00"),
    added(1),
    mock(notification, [device.requestNotificationPermission, { result: "accepted" }]),
    at("2026-10-25T10:05:00+09:00"),
    restart(),
    ...grants,
  ],
);

export const asksPermissionAgainOnStartWhileAsking = scenario(
  "Restart the server while notifier waits for the answer to its permission request; the restart discards the request, notifier requests permission again, and the user's choice answers the new request",
  [at("2026-10-25T10:00:00+09:00"), added(1), at("2026-10-25T10:05:00+09:00"), restart(), ...grants],
);

export const asksNoPermissionAfterStartWhenDecided = scenario(
  "Restart the server after permission is decided, and add a task; notifier does not request permission",
  [at("2026-10-25T10:00:00+09:00"), added(1), ...grants, restart(), added(2)],
);

export const asksNoPermissionOnStartWithoutOpenTasks = scenario(
  "Complete the only open task before the user chooses permission, and restart the server; notifier does not request permission again",
  [
    at("2026-10-25T10:00:00+09:00"),
    added(1),
    mock(notification, [device.requestNotificationPermission, { result: "accepted" }]),
    receive(todo.taskCompleted, { taskId: "task-1" }),
    at("2026-10-25T10:05:00+09:00"),
    restart(),
  ],
);
