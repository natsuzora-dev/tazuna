import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { closeTasks } from "./closer.ts";

export const closeOnce = scenario("Close the tasks; test reports assignRead", [
  at("2026-10-25T09:00:00+09:00"),
  send(closeTasks, {}),
]);
