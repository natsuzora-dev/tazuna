import { externalService } from "@natsuzora-dev/tazuna";

export const { command, contract } = externalService({ name: "device", description: "Ask the user for permissions" });

export const requestPermission = command({
  callers: ["app"],
  emits: [],
  rejects: ["invalid-input", "requires", "unavailable", "reused-id"],
});
