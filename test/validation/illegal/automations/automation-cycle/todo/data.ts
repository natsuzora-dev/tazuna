import { service } from "@natsuzora-dev/tazuna";

export const { automation, command, machine, event, contract } = service({
  name: "todo",
  description: "Keep the tasks",
});
