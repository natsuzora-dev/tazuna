import { externalService } from "@natsuzora-dev/tazuna";

export const { command, event } = externalService({ description: "Ask the user for notification permission" });

export const granted = event({});

export const requestPermission = command({
  emits: [granted],
  rejects: ["invalid-input", "requires", "unavailable", "reused-id"],
});
