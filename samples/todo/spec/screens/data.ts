import { service } from "@natsuzora-dev/tazuna";

export const { screen, contract, given, scenario } = service({
  name: "screens",
  description: "Show the task list and the task details",
});
