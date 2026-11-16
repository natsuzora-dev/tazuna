import { service } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";

export const { machine, scenario } = service({ description: "Use the device" });

export const permission = machine({
  description: "Ask for the permission when the service begins",
  commands: { requestPermission: device.requestPermission },
  initial: "asking",
  states: { asking: {}, asked: {} },
}).chart({
  states: { asking: { sends: { requestPermission: { onAccepted: [{ target: "asked" }], onRejected: [] } } } },
});
