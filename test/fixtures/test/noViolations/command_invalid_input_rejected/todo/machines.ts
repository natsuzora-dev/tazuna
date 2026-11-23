import { device } from "../device/contract.ts";
import { machine, taskAdded } from "./todo.ts";

export const notifier = machine({
  description:
    "Notify the device when a task is added, and notify again a minute later when the device rejects with unavailable",
  receives: { taskAdded },
  commands: { showNotification: device.showNotification },
  initial: "idle",
  states: { idle: {}, notifying: {}, retrying: {} },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ target: "notifying" }] } },
    notifying: {
      sends: {
        showNotification: {
          input: () => ({ text: "Added a task" }),
          onAccepted: [{ target: "idle" }],
          onRejected: [
            { guard: { isUnavailable: ({ rejection }) => rejection.kind === "unavailable" }, target: "retrying" },
            { target: "idle" },
          ],
        },
      },
    },
    retrying: { after: { minute: { delay: 60_000, onFired: [{ target: "notifying" }] } } },
  },
});
