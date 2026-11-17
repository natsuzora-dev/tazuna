import { service } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";

export const { machine, scenario } = service({ name: "app", description: "Use the device" });

export const permission = machine({
  description: "Ask for the permission when the service begins",
  receives: { granted: device.granted },
  commands: { requestPermission: device.requestPermission },
  initial: "asking",
  states: { asking: {}, asked: {}, allowed: {} },
}).chart({
  states: {
    asking: { sends: { requestPermission: { onAccepted: [{ target: "asked" }], onRejected: [] } } },
    asked: { on: { granted: [{ target: "allowed" }] } },
  },
});
