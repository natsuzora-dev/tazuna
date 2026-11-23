import { service } from "@natsuzora-dev/tazuna";

export const { automation, command, event, contract } = service({
  name: "notifier",
  description: "Notify about tasks",
});
