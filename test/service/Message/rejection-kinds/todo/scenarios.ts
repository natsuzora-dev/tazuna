import { at, call, mock, scenario, send, unchecked } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { notifier } from "./machines.ts";
import { addTask, completeTask, swapTitles, titledCount } from "./todo.ts";

const shown = mock(notifier, [device.showNotification, { result: "accepted" }]);

export const commandRejections = scenario(
  "Add a task with an empty title, complete a missing task, add tasks with a duplicate key and a duplicate unique title, and complete a task twice; todo rejects them with invalid-input, not-found, already-exists, and, for the second completion, requires with the condition name isOpen",
  [
    at("2026-10-25T10:00:00+09:00"),
    send(addTask, { taskId: "task-1", title: "" }),
    send(completeTask, { taskId: "task-9" }),
    send(addTask, { taskId: "task-1", title: "Buy milk" }),
    shown,
    send(addTask, { taskId: "task-1", title: "Buy eggs" }),
    send(addTask, { taskId: "task-2", title: "Buy milk" }),
    send(completeTask, { taskId: "task-1" }),
    send(completeTask, { taskId: "task-1" }),
  ],
);

export const queryRejections = scenario(
  "Ask for titledCount with a title that is not a string, with an empty title, and with a title; todo rejects the first with invalid-input and the second, for which the requires condition hasTitle fails, with requires and the condition name",
  [
    at("2026-10-25T10:00:00+09:00"),
    call(titledCount, { title: unchecked(1) }),
    call(titledCount, { title: "" }),
    call(titledCount, { title: "Buy milk" }),
  ],
);

export const unavailableAnswer = scenario(
  "Add a task, reject the notification with unavailable, and accept it a minute later; the guard of onRejected of notifier reads the rejection kind and goes to retrying, which requests the notification again a minute later",
  [
    at("2026-10-25T10:00:00+09:00"),
    send(addTask, { taskId: "task-1", title: "Buy milk" }),
    mock(notifier, [device.showNotification, { result: "rejected", rejection: { kind: "unavailable" } }]),
    at("2026-10-25T10:01:00+09:00"),
    shown,
  ],
);

export const swappedTitles = scenario(
  "Add two tasks and swap their titles; the first event of swapTitles makes two tasks share the unique title until the second event is written. todo checks duplicates when the command ends, so it accepts swapTitles",
  [
    at("2026-10-25T10:00:00+09:00"),
    send(addTask, { taskId: "task-1", title: "Buy milk" }),
    shown,
    send(addTask, { taskId: "task-2", title: "Buy eggs" }),
    shown,
    send(swapTitles, { firstId: "task-1", secondId: "task-2" }),
  ],
);
