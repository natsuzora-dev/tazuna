import {
  type AnswerOf,
  accepted,
  external,
  type OutRequest,
  type ProcessingLine,
  rejected,
  requested,
  requestOf,
  run,
} from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { device } from "../device/contract.ts";
import { todo } from "../todo/contract.ts";
import { given, scenario } from "./data.ts";

const fresh = given({
  start: "2026-10-25T10:00:00+09:00",
  records: { OpenTask: [], NotificationPermission: { status: "undetermined" } },
  peers: [run(todo, { Task: [], Settings: { shouldRemind: true } }), external(calendar), external(device)],
});

const show = (openTasks: number) => requestOf(device.showNotification, { text: `You have ${openTasks} open tasks` });
const askPermission = requestOf(device.requestNotificationPermission, {});

const taskAddedReaches = fresh.step((w, n: number) => {
  const adding = w.client.send(todo.addTask, { taskId: `task-${n}`, title: `Task ${n}` });
  const asking = adding.request(calendar.nextBusinessDay);
  w.net.deliver(asking);
  w.peer.calendar.leaveUnanswered(asking);
  return w.net.deliver(w.peer.todo.emit(todo.taskAdded, { taskId: `task-${n}` }, { resultOf: adding }));
});

const taskCompletedReaches = fresh.step((w, n: number) => {
  const completing = w.client.send(todo.completeTask, { taskId: `task-${n}` });
  return w.net.deliver(w.peer.todo.emit(todo.taskCompleted, { taskId: `task-${n}` }, { resultOf: completing }));
});

const asked = (line: ProcessingLine) => line.request(device.requestNotificationPermission);

const shownUnanswered = fresh.step((w, line: ProcessingLine) => {
  const showing = line.request(device.showNotification);
  w.net.deliver(showing);
  w.peer.device.leaveUnanswered(showing);
});

type DeviceEvent = typeof device.notificationPermissionGranted | typeof device.notificationPermissionDenied;

const deviceTells = fresh.step(
  (w, event: DeviceEvent, resultOf: OutRequest<typeof device.requestNotificationPermission> | null) => {
    w.net.deliver(w.peer.device.emit(event, {}, { resultOf }));
  },
);

const deviceGrants = fresh.step((w, asking: OutRequest<typeof device.requestNotificationPermission>) => {
  w.net.deliver(asking);
  w.net.deliver(w.peer.device.answer(asking, accepted));
  deviceTells(w, device.notificationPermissionGranted, asking);
});

const deviceAnswers = fresh.step(
  (
    w,
    asking: OutRequest<typeof device.requestNotificationPermission | typeof device.showNotification>,
    answer: AnswerOf<typeof device.requestNotificationPermission | typeof device.showNotification>,
  ) => {
    w.net.deliver(asking);
    w.net.deliver(w.peer.device.answer(asking, answer));
  },
);

export const warnsWhenTooMany = scenario({
  description: "Add too many open tasks and let 1 hour pass while they stay too many; notifier warns, and warns again",
  given: fresh,
  when: (w) => {
    deviceGrants(w, asked(taskAddedReaches(w, 0)));
    for (let n = 1; n <= 9; n += 1) taskAddedReaches(w, n);
    // task-0 to task-10 are 11 open tasks, one more than notifier allows.
    const tooMany = taskAddedReaches(w, 10);
    shownUnanswered(w, tooMany);
    // task-0 to task-11 are 12 open tasks an hour and a half later.
    taskAddedReaches(w, 11);
    const later = w.clock.at("2026-10-25T11:30:00+09:00");
    shownUnanswered(w, later);
    taskCompletedReaches(w, 0);
    return { tooMany, later };
  },
  then: ({ tooMany, later }) => [requested(tooMany, [show(11)]), requested(later, [show(12)])],
});

export const warnsAgainAfterNotificationAnswered = scenario({
  description:
    "Add too many open tasks, let device fail to show the warning, and let 1 hour pass; notifier shows the warning again",
  given: fresh,
  when: (w) => {
    deviceGrants(w, asked(taskAddedReaches(w, 0)));
    for (let n = 1; n <= 9; n += 1) taskAddedReaches(w, n);
    const tooMany = taskAddedReaches(w, 10);
    // task-0 to task-11 are 12 open tasks an hour later.
    taskAddedReaches(w, 11);
    deviceAnswers(w, tooMany.request(device.showNotification), rejected("unavailable"));
    const hour = w.clock.at("2026-10-25T11:00:00+09:00");
    deviceAnswers(w, hour.request(device.showNotification), accepted);
    return { hour };
  },
  then: ({ hour }) => [requested(hour, [show(12)])],
});

export const warnsWithoutNotificationWhileAsking = scenario({
  description:
    "While requestNotificationPermission waits for its answer, let the user grant permission in the device settings and add too many open tasks; notifier shows no notification",
  given: fresh,
  when: (w) => {
    const asking = asked(taskAddedReaches(w, 0));
    // Granted in the device settings, not as the result of a request.
    deviceTells(w, device.notificationPermissionGranted, null);
    for (let n = 1; n <= 9; n += 1) taskAddedReaches(w, n);
    const tooMany = taskAddedReaches(w, 10);
    taskAddedReaches(w, 11);
    deviceAnswers(w, asking, accepted);
    return { tooMany };
  },
  then: ({ tooMany }) => [requested(tooMany, [])],
});

export const countsReopenedTask = scenario({
  description: "Complete a task and reopen it; notifier counts the task again",
  given: fresh,
  when: (w) => {
    deviceGrants(w, asked(taskAddedReaches(w, 1)));
    for (let n = 2; n <= 10; n += 1) taskAddedReaches(w, n);
    w.clock.at("2026-10-25T10:01:00+09:00");
    taskCompletedReaches(w, 1);
    // task-2 to task-11 are 10 open tasks, which notifier allows.
    const eleventh = taskAddedReaches(w, 11);
    const reopening = w.client.send(todo.reopenTask, { taskId: "task-1" });
    // task-1 open again makes 11.
    const reopened = w.net.deliver(w.peer.todo.emit(todo.taskReopened, { taskId: "task-1" }, { resultOf: reopening }));
    shownUnanswered(w, reopened);
    return { eleventh, reopened };
  },
  then: ({ eleventh, reopened }) => [requested(eleventh, []), requested(reopened, [show(11)])],
});

export const warnsWithoutNotificationWhenDenied = scenario({
  description: "Let the user deny permission and add too many open tasks; notifier shows no notification",
  given: fresh,
  when: (w) => {
    const asking = asked(taskAddedReaches(w, 0));
    deviceAnswers(w, asking, accepted);
    deviceTells(w, device.notificationPermissionDenied, asking);
    for (let n = 1; n <= 9; n += 1) taskAddedReaches(w, n);
    const tooMany = taskAddedReaches(w, 10);
    taskAddedReaches(w, 11);
    return { tooMany };
  },
  then: ({ tooMany }) => [requested(tooMany, [])],
});

export const ignoresRedelivery = scenario({
  description: "Deliver an event twice through the network; notifier counts it once",
  given: fresh,
  when: (w) => {
    const first = taskAddedReaches(w, 1);
    const asking = asked(first);
    w.net.deliver(asking);
    w.peer.device.leaveUnanswered(asking);
    const again = w.net.redeliver(first);
    return { first, again };
  },
  then: ({ first, again }) => [requested(first, [askPermission]), requested(again, [])],
});

export const asksPermissionAgain = scenario({
  description:
    "Let device fail to request permission, then let the user grant it; notifier requests at most 3 times 1 minute apart, and requests no more after the grant",
  given: fresh,
  when: (w) => {
    deviceAnswers(w, asked(taskAddedReaches(w, 1)), rejected("unavailable"));
    const retry1 = w.clock.at("2026-10-25T10:01:00+09:00");
    deviceAnswers(w, asked(retry1), rejected("unavailable"));
    const retry2 = w.clock.at("2026-10-25T10:02:00+09:00");
    deviceAnswers(w, asked(retry2), rejected("unavailable"));
    const noRetry = w.clock.at("2026-10-25T10:03:00+09:00");
    const second = taskAddedReaches(w, 2);
    deviceGrants(w, asked(second));
    const third = taskAddedReaches(w, 3);
    return { noRetry, second, third };
  },
  then: ({ noRetry, second, third }) => [
    requested(noRetry, []),
    requested(second, [askPermission]),
    requested(third, []),
  ],
});

export const warnsWithoutNotificationAfterRevoked = scenario({
  description:
    "Let the user grant permission and revoke it in the device settings, and add too many open tasks; notifier shows no notification",
  given: fresh,
  when: (w) => {
    deviceGrants(w, asked(taskAddedReaches(w, 0)));
    deviceTells(w, device.notificationPermissionDenied, null);
    for (let n = 1; n <= 9; n += 1) taskAddedReaches(w, n);
    const tooMany = taskAddedReaches(w, 10);
    taskAddedReaches(w, 11);
    return { tooMany };
  },
  then: ({ tooMany }) => [requested(tooMany, [])],
});

export const stopsAskingWhenGrantedWhileRetrying = scenario({
  description:
    "While notifier waits to request permission again, let the user grant it in the device settings; notifier requests no more",
  given: fresh,
  when: (w) => {
    deviceAnswers(w, asked(taskAddedReaches(w, 1)), rejected("unavailable"));
    deviceTells(w, device.notificationPermissionGranted, null);
    const minute = w.clock.at("2026-10-25T10:01:00+09:00");
    return { minute };
  },
  then: ({ minute }) => [requested(minute, [])],
});

export const warnsAgainOnStart = scenario({
  description: "Add too many open tasks and restart the server within 1 hour of the warning; notifier warns again",
  given: fresh,
  when: (w) => {
    deviceGrants(w, asked(taskAddedReaches(w, 0)));
    for (let n = 1; n <= 9; n += 1) taskAddedReaches(w, n);
    const tooMany = taskAddedReaches(w, 10);
    shownUnanswered(w, tooMany);
    // task-0 to task-11 are 12 open tasks at the restart.
    taskAddedReaches(w, 11);
    w.clock.at("2026-10-25T10:10:00+09:00");
    const restart = w.host.restart();
    shownUnanswered(w, restart);
    return { restart };
  },
  then: ({ restart }) => [requested(restart, [show(12)])],
});

export const asksPermissionAgainOnStart = scenario({
  description:
    "Restart the server while a task is open and before the user chooses permission; notifier requests permission again",
  given: fresh,
  when: (w) => {
    deviceAnswers(w, asked(taskAddedReaches(w, 1)), accepted);
    w.clock.at("2026-10-25T10:05:00+09:00");
    const restart = w.host.restart();
    deviceGrants(w, asked(restart));
    return { restart };
  },
  then: ({ restart }) => [requested(restart, [askPermission])],
});

export const asksPermissionAgainOnStartWhileAsking = scenario({
  description:
    "Restart the server while notifier waits for the answer to its permission request; the restart discards the request, notifier requests permission again, and the user's choice answers the new request",
  given: fresh,
  when: (w) => {
    const asking = asked(taskAddedReaches(w, 1));
    w.net.deliver(asking);
    w.peer.device.leaveUnanswered(asking);
    w.clock.at("2026-10-25T10:05:00+09:00");
    const restart = w.host.restart();
    deviceGrants(w, asked(restart));
    return { restart };
  },
  then: ({ restart }) => [requested(restart, [askPermission])],
});

export const asksNoPermissionAfterStartWhenDecided = scenario({
  description: "Restart the server after permission is decided, and add a task; notifier does not request permission",
  given: fresh,
  when: (w) => {
    deviceGrants(w, asked(taskAddedReaches(w, 1)));
    const restart = w.host.restart();
    const second = taskAddedReaches(w, 2);
    return { restart, second };
  },
  then: ({ restart, second }) => [requested(restart, []), requested(second, [])],
});

export const asksNoPermissionOnStartWithoutOpenTasks = scenario({
  description:
    "Complete the only open task before the user chooses permission, and restart the server; notifier does not request permission again",
  given: fresh,
  when: (w) => {
    deviceAnswers(w, asked(taskAddedReaches(w, 1)), accepted);
    taskCompletedReaches(w, 1);
    w.clock.at("2026-10-25T10:05:00+09:00");
    const restart = w.host.restart();
    return { restart };
  },
  then: ({ restart }) => [requested(restart, [])],
});
