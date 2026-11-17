import { type Caused, external, raw, type When } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { addTask, completeTask, scenario, swapTitles, titledCount } from "./todo.ts";

const peers = { device: external(device) } as const;
const given = { start: "2026-10-25T10:00:00+09:00", records: { Task: [] }, peers } as const;

const deliverAndAccept = (w: When<typeof peers>, line: Caused) => {
  const notification = line.request(device.showNotification);
  w.net.deliver(notification);
  w.net.deliver(w.peer.device.answer(notification, { result: "accepted" }));
};

export const commandRejections = scenario(
  "Add a task with an empty title, complete a missing task, add tasks with a duplicate key and a duplicate unique title, and complete a task twice; todo rejects them with invalid-input, not-found, already-exists, and, for the second completion, requires with the condition name isOpen",
  {
    given,
    when: (w) => {
      w.client.send(addTask, { taskId: "task-1", title: "" });
      w.client.send(completeTask, { taskId: "task-9" });
      deliverAndAccept(w, w.client.send(addTask, { taskId: "task-1", title: "Buy milk" }));
      w.client.send(addTask, { taskId: "task-1", title: "Buy eggs" });
      w.client.send(addTask, { taskId: "task-2", title: "Buy milk" });
      w.client.send(completeTask, { taskId: "task-1" });
      w.client.send(completeTask, { taskId: "task-1" });
    },
    then: () => [],
  },
);

export const queryRejections = scenario(
  "Ask for titledCount with a title that is not a string, with an empty title, and with a title; todo rejects the first with invalid-input and the second, for which the requires condition hasTitle fails, with requires and the condition name",
  {
    given,
    when: (w) => {
      w.client.call(titledCount, raw({ title: 1 }));
      w.client.call(titledCount, { title: "" });
      w.client.call(titledCount, { title: "Buy milk" });
    },
    then: () => [],
  },
);

export const unavailableAnswer = scenario(
  "Add a task, reject the notification with unavailable, and accept it a minute later; the guard of onRejected of notifier reads the rejection kind and goes to retrying, which requests the notification again a minute later",
  {
    given,
    when: (w) => {
      const add = w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
      const notification = add.request(device.showNotification);
      w.net.deliver(notification);
      w.net.deliver(w.peer.device.answer(notification, { result: "rejected", rejection: { kind: "unavailable" } }));
      deliverAndAccept(w, w.clock.at("2026-10-25T10:01:00+09:00"));
    },
    then: () => [],
  },
);

export const swappedTitles = scenario(
  "Add two tasks and swap their titles; the first event of swapTitles makes two tasks share the unique title until the second event is written. todo checks duplicates when the command ends, so it accepts swapTitles",
  {
    given,
    when: (w) => {
      deliverAndAccept(w, w.client.send(addTask, { taskId: "task-1", title: "Buy milk" }));
      deliverAndAccept(w, w.client.send(addTask, { taskId: "task-2", title: "Buy eggs" }));
      w.client.send(swapTitles, { firstId: "task-1", secondId: "task-2" });
    },
    then: () => [],
  },
);
