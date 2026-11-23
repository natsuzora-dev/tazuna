import { externalService } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, contract } = externalService({
  name: "device",
  description: "Show notifications and play sounds",
});

export const showNotification = command({
  callers: ["todo"],
  input: { text: z.string() },
  emits: [],
  rejects: ["invalid-input", "requires", "unavailable", "reused-id"],
});

export const playSound = command({
  callers: [],
  emits: [],
  rejects: ["invalid-input", "requires", "unavailable", "reused-id"],
});
