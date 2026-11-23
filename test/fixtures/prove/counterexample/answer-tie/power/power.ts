import { externalService } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, event, contract } = externalService({
  name: "power",
  description: "Switch the mains of a lamp",
});

export const turnOn = command({ callers: ["lamp"], emits: [], rejects: ["unavailable"] });

export const cut = event({ payload: { reason: z.enum(["storm", "fault"]) } });
