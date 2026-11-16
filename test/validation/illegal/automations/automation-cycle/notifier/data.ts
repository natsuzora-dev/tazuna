import { service } from "@natsuzora-dev/tazuna";

export const { automation, command, event, contract } = service({ description: "Notify about tasks" });
