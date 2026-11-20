import { externalService } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, contract } = externalService({ name: "device", description: "Notify the user" });

export const notify = command({ input: { text: z.string() }, emits: [], rejects: ["unavailable"] });
export const beep = command({ emits: [], rejects: [] });
