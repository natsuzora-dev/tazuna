import { ref } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { machine, Task } from "./todo.ts";

export const notifier = machine({
  description: "Notify the device of the id of each task",
  commands: { showNotification: device.showNotification },
  initial: "notifying",
  states: {
    notifying: {
      type: "map",
      key: { taskId: ref(Task) },
      initial: "showing",
      states: { showing: {}, shown: {} },
    },
  },
}).chart({
  states: {
    notifying: { items: ({ records }) => records.Task.map((t) => ({ taskId: t.id })) },
    showing: {
      sends: {
        showNotification: {
          input: ({ key }) => ({ text: key.taskId }),
          onAccepted: [{ target: "shown" }],
          onRejected: [{ target: "shown" }],
        },
      },
    },
  },
});
