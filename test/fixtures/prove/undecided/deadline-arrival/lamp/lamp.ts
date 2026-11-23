import { service } from "@natsuzora-dev/tazuna";
import { power } from "../power/contract.ts";

export const { machine } = service({
  name: "lamp",
  description: "Ask for the mains and give up after a second, so the answer and the timeout can come at one instant",
});

export const switcher = machine({
  description: "Wait a second for the mains to turn on",
  commands: { turnOn: power.turnOn },
  initial: "asking",
  states: { asking: {}, lit: {}, dark: {} },
}).chart({
  states: {
    asking: {
      sends: { turnOn: { onAccepted: [{ target: "lit" }], onRejected: [{ target: "dark" }] } },
      after: { timeout: { delay: 1000, onFired: [{ target: "dark" }] } },
    },
  },
});
