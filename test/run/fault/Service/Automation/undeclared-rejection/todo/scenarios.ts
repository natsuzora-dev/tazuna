import { external } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { addTask, scenario } from "./todo.ts";

export const notificationAwaited = scenario(
  "Add a task and leave the device's answer to the notification open; showNotification declares no rejection kinds, so test appends no rejected answer and reports nothing",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: { device: external(device) } },
    when: (w) => {
      const l0 = w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
      w.net.leaveInFlight(l0.request(device.showNotification));
    },
    then: () => [],
  },
);
