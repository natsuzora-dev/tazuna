import { at, operate, scenario } from "@natsuzora-dev/tazuna";
import { listScreen } from "./listScreen.ts";

export const showAll = scenario(
  "Operate showAll; open and its child allTasks both show tasks, and the shows of the innermost state applies, so listScreen ends the subscription with the filter open and subscribes with the filter all",
  [at("2026-10-25T10:00:00+09:00"), operate(listScreen, "showAll")],
);
