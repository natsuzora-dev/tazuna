import { externalService } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, contract } = externalService({ description: "Show notifications" });

export const showNotification = command({ input: { text: z.string() }, emits: [], rejects: [] });
