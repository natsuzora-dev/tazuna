import { service } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";

export const { machine, scenario } = service({ name: "app", description: "Use the device" });

export const permission = machine({
  description: "Ask for the permission once, at the start",
  receives: { granted: device.granted },
  commands: { requestPermission: device.requestPermission },
  initial: "asking",
  states: { asking: {}, answering: {}, allowed: { type: "final" }, refused: { type: "final" } },
}).chart({
  states: {
    asking: {
      sends: { requestPermission: { onAccepted: [{ target: "answering" }], onRejected: [{ target: "refused" }] } },
    },
    answering: { on: { granted: [{ target: "allowed" }] } },
  },
});
