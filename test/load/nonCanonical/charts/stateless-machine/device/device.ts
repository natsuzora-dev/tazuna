import { externalService } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command } = externalService({ description: "Show notifications and play sounds" });

export const showNotification = command({
  input: { text: z.string() },
  emits: [],
  rejects: ["invalid-input", "requires", "unavailable", "reused-id"],
});

export const playSound = command({ emits: [], rejects: ["invalid-input", "requires", "unavailable", "reused-id"] });
