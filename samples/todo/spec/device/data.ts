import { externalService } from "@natsuzora-dev/tazuna";

export const { command, event, contract } = externalService({
  name: "device",
  description: "Show notifications to the user and request permission to show them",
});
