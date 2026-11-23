import { externalService } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, contract } = externalService({ name: "device", description: "Show notifications" });

export const showNotification = command({
  callers: ["todo"],
  input: { text: z.string() },
  emits: [],
  rejects: ["invalid-input", "requires", "unavailable", "reused-id"],
});
