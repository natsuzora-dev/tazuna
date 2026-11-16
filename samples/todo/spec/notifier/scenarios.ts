import { type Caused, external, type OutRequest, request, requested, run, type When } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { device } from "../device/contract.ts";
import { todo } from "../todo/contract.ts";
import { scenario } from "./data.ts";

const peers = {
  todo: run(todo, { Task: [], Settings: { shouldRemind: true } }),
  calendar: external(calendar),
  device: external(device),
} as const;
type W = When<typeof peers>;

const fresh = {
  start: "2026-10-25T10:00:00+09:00",
  records: { OpenTask: [], NotificationPermission: { status: "undetermined" } },
  peers,
} as const;

const accepted = { result: "accepted" } as const;
const unavailable = { result: "rejected", rejection: { kind: "unavailable" } } as const;
const show = (n: number) => request(device.showNotification, { text: `You have ${n} open tasks` });
const askPermission = request(device.requestNotificationPermission, {});

/**
 * Another caller adds task-n in todo; todo's run asks calendar, which never answers here, and todo's taskAdded, the
 * result of that addTask, reaches notifier. Returns the delivering line.
 */
const added = (w: W, n: number) => {
  const add = w.client.send(todo.addTask, { taskId: `task-${n}`, title: `Task ${n}` });
  w.peer.calendar.leaveUnanswered(add.request(calendar.nextBusinessDay));
  return w.peer.todo.emit(todo.taskAdded, { taskId: `task-${n}` }, { resultOf: add });
};
const addedRange = (w: W, from: number, to: number) =>
  Array.from({ length: to - from + 1 }, (_, i) => added(w, from + i));
const completed = (w: W, n: number) => {
  const complete = w.client.send(todo.completeTask, { taskId: `task-${n}` });
  return w.peer.todo.emit(todo.taskCompleted, { taskId: `task-${n}` }, { resultOf: complete });
};

/** The permission request that `line` caused. */
const asked = (line: Caused) => line.request(device.requestNotificationPermission);

/** device accepts the permission request, and the user's grant arrives as its result. */
const grants = (w: W, request: OutRequest<typeof device.requestNotificationPermission>) => {
  w.peer.device.answer(request, accepted);
  return w.peer.device.emit(device.notificationPermissionGranted, {}, { resultOf: request });
};

/** task-0 is open and permission is granted. */
const grantedWithTask0 = (w: W) => {
  const first = added(w, 0);
  grants(w, asked(first));
};

/** Tasks 1..11 are added after task-0; returns the line that delivers task-10's taskAdded, the 11th open task. */
const tooManyTasks = (w: W) => {
  addedRange(w, 1, 9);
  const eleventh = added(w, 10);
  added(w, 11);
  return eleventh;
};

export const warnsWhenTooMany = scenario(
  "Add too many open tasks and let 1 hour pass while they stay too many; notifier warns, and warns again",
  {
    given: fresh,
    when: (w) => {
      grantedWithTask0(w);
      const tooMany = tooManyTasks(w);
      w.peer.device.leaveUnanswered(tooMany.request(device.showNotification));
      const later = w.clock.at("2026-10-25T11:30:00+09:00");
      w.peer.device.leaveUnanswered(later.request(device.showNotification));
      completed(w, 0);
      return { tooMany, later };
    },
    then: ({ tooMany, later }) => [requested(tooMany, [show(11)]), requested(later, [show(12)])],
  },
);

export const warnsAgainAfterNotificationAnswered = scenario(
  "Add too many open tasks, let device fail to show the warning, and let 1 hour pass; notifier shows the warning again",
  {
    given: fresh,
    when: (w) => {
      grantedWithTask0(w);
      const tooMany = tooManyTasks(w);
      w.peer.device.answer(tooMany.request(device.showNotification), unavailable);
      const hour = w.clock.at("2026-10-25T11:00:00+09:00");
      w.peer.device.answer(hour.request(device.showNotification), accepted);
      return { hour };
    },
    then: ({ hour }) => [requested(hour, [show(12)])],
  },
);

export const warnsWithoutNotificationWhileAsking = scenario(
  "While requestNotificationPermission waits for its answer, let the user grant permission in the device settings and add too many open tasks; notifier shows no notification",
  {
    given: fresh,
    when: (w) => {
      const first = added(w, 0);
      // Granted in the device settings, not as the result of a request.
      w.peer.device.emit(device.notificationPermissionGranted, {}, { resultOf: null });
      const tooMany = tooManyTasks(w);
      w.peer.device.answer(asked(first), accepted);
      return { tooMany };
    },
    then: ({ tooMany }) => [requested(tooMany, [])],
  },
);

export const countsReopenedTask = scenario("Complete a task and reopen it; notifier counts the task again", {
  given: fresh,
  when: (w) => {
    const first = added(w, 1);
    grants(w, asked(first));
    addedRange(w, 2, 10);
    w.clock.at("2026-10-25T10:01:00+09:00");
    completed(w, 1);
    const eleventh = added(w, 11);
    const reopen = w.client.send(todo.reopenTask, { taskId: "task-1" });
    const reopened = w.peer.todo.emit(todo.taskReopened, { taskId: "task-1" }, { resultOf: reopen });
    w.peer.device.leaveUnanswered(reopened.request(device.showNotification));
    return { eleventh, reopened };
  },
  then: ({ eleventh, reopened }) => [requested(eleventh, []), requested(reopened, [show(11)])],
});

export const warnsWithoutNotificationWhenDenied = scenario(
  "Let the user deny permission and add too many open tasks; notifier shows no notification",
  {
    given: fresh,
    when: (w) => {
      const first = added(w, 0);
      const request = asked(first);
      w.peer.device.answer(request, accepted);
      w.peer.device.emit(device.notificationPermissionDenied, {}, { resultOf: request });
      const tooMany = tooManyTasks(w);
      return { tooMany };
    },
    then: ({ tooMany }) => [requested(tooMany, [])],
  },
);

export const ignoresRedelivery = scenario("Deliver an event twice through the network; notifier counts it once", {
  given: fresh,
  when: (w) => {
    const first = added(w, 1);
    w.peer.device.leaveUnanswered(asked(first));
    const again = w.net.redeliver(first);
    return { first, again };
  },
  then: ({ first, again }) => [requested(first, [askPermission]), requested(again, [])],
});

export const asksPermissionAgain = scenario(
  "Let device fail to request permission, then let the user grant it; notifier requests at most 3 times 1 minute apart, and requests no more after the grant",
  {
    given: fresh,
    when: (w) => {
      const first = added(w, 1);
      w.peer.device.answer(asked(first), unavailable);
      const retry1 = w.clock.at("2026-10-25T10:01:00+09:00");
      w.peer.device.answer(asked(retry1), unavailable);
      const retry2 = w.clock.at("2026-10-25T10:02:00+09:00");
      w.peer.device.answer(asked(retry2), unavailable);
      const noRetry = w.clock.at("2026-10-25T10:03:00+09:00");
      const second = added(w, 2);
      grants(w, asked(second));
      const third = added(w, 3);
      return { noRetry, second, third };
    },
    then: ({ noRetry, second, third }) => [
      requested(noRetry, []),
      requested(second, [askPermission]),
      requested(third, []),
    ],
  },
);

export const warnsWithoutNotificationAfterRevoked = scenario(
  "Let the user grant permission and revoke it in the device settings, and add too many open tasks; notifier shows no notification",
  {
    given: fresh,
    when: (w) => {
      grantedWithTask0(w);
      w.peer.device.emit(device.notificationPermissionDenied, {}, { resultOf: null });
      const tooMany = tooManyTasks(w);
      return { tooMany };
    },
    then: ({ tooMany }) => [requested(tooMany, [])],
  },
);

export const stopsAskingWhenGrantedWhileRetrying = scenario(
  "While notifier waits to request permission again, let the user grant it in the device settings; notifier requests no more",
  {
    given: fresh,
    when: (w) => {
      const first = added(w, 1);
      w.peer.device.answer(asked(first), unavailable);
      w.peer.device.emit(device.notificationPermissionGranted, {}, { resultOf: null });
      const minute = w.clock.at("2026-10-25T10:01:00+09:00");
      return { minute };
    },
    then: ({ minute }) => [requested(minute, [])],
  },
);

export const warnsAgainOnStart = scenario(
  "Add too many open tasks and restart the server within 1 hour of the warning; notifier warns again",
  {
    given: fresh,
    when: (w) => {
      grantedWithTask0(w);
      const tooMany = tooManyTasks(w);
      w.peer.device.leaveUnanswered(tooMany.request(device.showNotification));
      w.clock.at("2026-10-25T10:10:00+09:00");
      const restart = w.host.restart();
      w.peer.device.leaveUnanswered(restart.request(device.showNotification));
      return { restart };
    },
    then: ({ restart }) => [requested(restart, [show(12)])],
  },
);

export const asksPermissionAgainOnStart = scenario(
  "Restart the server while a task is open and before the user chooses permission; notifier requests permission again",
  {
    given: fresh,
    when: (w) => {
      const first = added(w, 1);
      w.peer.device.answer(asked(first), accepted);
      w.clock.at("2026-10-25T10:05:00+09:00");
      const restart = w.host.restart();
      grants(w, asked(restart));
      return { restart };
    },
    then: ({ restart }) => [requested(restart, [askPermission])],
  },
);

export const asksPermissionAgainOnStartWhileAsking = scenario(
  "Restart the server while notifier waits for the answer to its permission request; the restart discards the request, notifier requests permission again, and the user's choice answers the new request",
  {
    given: fresh,
    when: (w) => {
      const first = added(w, 1);
      w.peer.device.leaveUnanswered(asked(first));
      w.clock.at("2026-10-25T10:05:00+09:00");
      const restart = w.host.restart();
      grants(w, asked(restart));
      return { restart };
    },
    then: ({ restart }) => [requested(restart, [askPermission])],
  },
);

export const asksNoPermissionAfterStartWhenDecided = scenario(
  "Restart the server after permission is decided, and add a task; notifier does not request permission",
  {
    given: fresh,
    when: (w) => {
      const first = added(w, 1);
      grants(w, asked(first));
      const restart = w.host.restart();
      const second = added(w, 2);
      return { restart, second };
    },
    then: ({ restart, second }) => [requested(restart, []), requested(second, [])],
  },
);

export const asksNoPermissionOnStartWithoutOpenTasks = scenario(
  "Complete the only open task before the user chooses permission, and restart the server; notifier does not request permission again",
  {
    given: fresh,
    when: (w) => {
      const first = added(w, 1);
      w.peer.device.answer(asked(first), accepted);
      completed(w, 1);
      w.clock.at("2026-10-25T10:05:00+09:00");
      const restart = w.host.restart();
      return { restart };
    },
    then: ({ restart }) => [requested(restart, [])],
  },
);
