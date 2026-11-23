import { externalService } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, contract } = externalService({ name: "device", description: "Notify the user" });

export const notify = command({ callers: ["todo"], input: { text: z.string() }, emits: [], rejects: ["unavailable"] });
export const beep = command({ callers: [], emits: [], rejects: [] });
