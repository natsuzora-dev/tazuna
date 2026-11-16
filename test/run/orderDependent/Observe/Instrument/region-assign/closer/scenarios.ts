import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { closeTasks } from "./closer.ts";

export const closeOnce = scenario(
  "Close the tasks; each machine assigns notes in two regions or copies in one microstep, which have no order, so test reports bothAssign",
  [at("2026-10-25T09:00:00+09:00"), send(closeTasks, {})],
);
