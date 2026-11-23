import { externalService } from "@natsuzora-dev/tazuna";

export const { command, event, contract } = externalService({
  name: "device",
  description: "Ask the user for permissions",
});

export const granted = event({});
export const muted = event({});

export const requestPermission = command({
  callers: ["notifier"],
  emits: [granted],
  rejects: ["invalid-input", "requires", "unavailable", "reused-id"],
});
