import { externalService } from "@natsuzora-dev/tazuna";

export const { command, contract } = externalService({
  description: "Play sounds and mute the device, whose mute command is not exported",
});

export const playSound = command({ emits: [], rejects: ["invalid-input", "requires", "unavailable", "reused-id"] });

const mute = command({ emits: [], rejects: ["invalid-input", "requires", "unavailable", "reused-id"] });

export const device = contract({ playSound, mute });
