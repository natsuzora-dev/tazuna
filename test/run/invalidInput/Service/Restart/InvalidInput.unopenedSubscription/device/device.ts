import { externalService } from "@natsuzora-dev/tazuna";

export const { command, contract } = externalService({ name: "device", description: "Ask the user for permissions" });

export const requestPermission = command({
  emits: [],
  rejects: ["invalid-input", "requires", "unavailable", "reused-id"],
});
