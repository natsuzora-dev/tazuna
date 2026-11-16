import { service } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";

export const { machine } = service({ description: "Ask for notification permission" });

export const permission = machine({
  description: "Ask device for notification permission and wait until it is granted",
  receives: { granted: device.granted },
  commands: { requestPermission: device.requestPermission },
  initial: "asking",
  states: { asking: {}, answering: {}, allowed: { type: "final" } },
}).chart({
  states: {
    asking: {
      sends: {
        requestPermission: {
          onAccepted: [{ target: "answering" }],
          onRejected: [{ target: "asking", reenter: true }],
        },
      },
    },
    answering: { on: { granted: [{ target: "allowed" }] } },
  },
});
