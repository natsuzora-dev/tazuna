import { externalService } from "@natsuzora-dev/tazuna";

export const { command, contract } = externalService({ name: "power", description: "Switch the mains of a lamp" });

export const turnOn = command({ callers: ["lamp"], emits: [], rejects: ["unavailable"] });
