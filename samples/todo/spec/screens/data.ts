import { service } from "@natsuzora-dev/tazuna";

export const { screen, contract, scenario } = service({
  name: "screens",
  description: "Show the task list and the task details",
});
