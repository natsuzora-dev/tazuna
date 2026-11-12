import { externalService } from "@natsuzora-dev/tazuna";

export const { command, event } = externalService({
  description: "Show notifications to the user and request permission to show them",
});
