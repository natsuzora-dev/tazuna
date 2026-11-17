import { external } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { addTasks, scenario } from "./todo.ts";

export const twoCopies = scenario(
  "Add two tasks at once; notifier runs the copies of task-1 and task-2 in one addTasks and requests a notification in each copy. The two requests do not depend on each other, so verify treats as matching an implementation trace that sends the request of the copy of task-2 first; no violation",
  {
    given: { start: "2026-10-25T10:00:00+09:00", records: { Task: [] }, peers: { device: external(device) } },
    when: (w) => {
      const added = w.client.send(addTasks, { taskIds: ["task-1", "task-2"] });
      w.net.leaveInFlight(added.request(device.showNotification, { input: { text: "task-1" } }));
      w.net.leaveInFlight(added.request(device.showNotification, { input: { text: "task-2" } }));
    },
    then: () => [],
  },
);
