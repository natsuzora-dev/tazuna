import { externalService } from "@natsuzora-dev/tazuna";

export const { command, event, contract } = externalService({
  name: "power",
  description: "Switch the mains of a lamp",
});

export const turnOn = command({ callers: ["lamp"], emits: [], rejects: ["unavailable"] });

export const cut = event({});
