import { service } from "@natsuzora-dev/tazuna";

export const { automation, command, event } = service({ description: "Notify about tasks" });
