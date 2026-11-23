import { accepted, external, parseInstant, rejected } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { addTask, given, scenario } from "./todo.ts";

const arranged = given({
  start: parseInstant("2026-10-25T10:00:00+09:00"),
  records: { Task: [] },
  peers: [external(device)],
});

export const notifiedAfterAdd = scenario({
  description:
    "Add a task and accept the notification; notifyAdded reacts to taskAdded, sends device.showNotification as a request, and receives device's acceptance",
  given: arranged,
  when: (w) => {
    const add = w.client.as("client").send(addTask, { taskId: "task-1", title: "Buy milk" });
    const notification = add.request(device.showNotification);
    w.net.deliver(notification);
    w.net.deliver(w.peer.device.answer(notification, accepted()));
  },
  then: () => [],
});

export const ignoredUnavailable = scenario({
  description:
    "Add a task and reject the notification with unavailable; notifyAdded ignores the rejection by onRejected: [], so no violation is reported",
  given: arranged,
  when: (w) => {
    const add = w.client.as("client").send(addTask, { taskId: "task-1", title: "Buy milk" });
    const notification = add.request(device.showNotification);
    w.net.deliver(notification);
    w.net.deliver(w.peer.device.answer(notification, rejected("unavailable")));
  },
  then: () => [],
});
