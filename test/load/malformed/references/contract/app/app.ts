import { service } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";

export const { machine } = service({ name: "app", description: "Play a sound, then mute the device" });

export const player = machine({
  description: "Play a sound, then mute the device",
  commands: { playSound: device.playSound, mute: device.mute },
  initial: "playing",
  states: { playing: {}, muting: {}, done: { type: "final" } },
}).chart({
  states: {
    playing: { sends: { playSound: { onAccepted: [{ target: "muting" }], onRejected: [{ target: "done" }] } } },
    muting: { sends: { mute: { onAccepted: [{ target: "done" }], onRejected: [{ target: "done" }] } } },
  },
});
