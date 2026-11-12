import { at, cannotOperate, operate, restart, scenario } from "@natsuzora-dev/tazuna";
import { homeScreen, taskListScreen } from "./screens.ts";

export const screensReopen = scenario(
  "Open the list and restart; the restart closes taskListScreen without ending its subscription to tasks, and homeScreen opens again in home, so the list cannot be closed and homeScreen accepts openList, which subscribes to tasks again",
  [
    at("2026-10-25T10:00:00+09:00"),
    operate(homeScreen, "openList"),
    restart(),
    cannotOperate(taskListScreen, "close"),
    operate(homeScreen, "openList"),
  ],
);
