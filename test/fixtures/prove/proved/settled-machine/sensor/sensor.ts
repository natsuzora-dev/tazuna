import { externalService } from "@natsuzora-dev/tazuna";

export const { command, event, contract } = externalService({ name: "sensor", description: "Report a door" });

export const opened = event({});
export const knocked = event({});
export const ring = command({ callers: ["panel"], emits: [], rejects: ["unavailable"] });
