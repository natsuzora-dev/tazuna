import { externalService } from "@natsuzora-dev/tazuna";

export const { command } = externalService({ description: "Ask the user for permissions" });

export const requestPermission = command({
  emits: [],
  rejects: ["invalid-input", "requires", "unavailable", "reused-id"],
});
