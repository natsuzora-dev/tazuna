import { at, operate, scenario } from "@natsuzora-dev/tazuna";
import { helpPanel, homeScreen, taskListScreen } from "./screens.ts";

export const listClosedByParent = scenario(
  "Open the list at 10:00 and again at 10:02; homeScreen opens one taskListScreen each time it enters listing, and when it exits listing at the one-minute deadline at 10:01, it closes taskListScreen, which ends its subscription to tasks. homeScreen keeps its subscription to taskCount while taskListScreen is open",
  [
    at("2026-10-25T10:00:00+09:00"),
    operate(homeScreen, "openList"),
    at("2026-10-25T10:02:00+09:00"),
    operate(homeScreen, "openList"),
  ],
);

export const modalChild = scenario(
  "Open the list, close it, and count all; taskListScreen, which homeScreen opened as modal, closes on the operation close, and homeScreen goes back to home through onDone, accepts the operation countAll, and subscribes to taskCount again with all",
  [
    at("2026-10-25T10:00:00+09:00"),
    operate(homeScreen, "openList"),
    operate(taskListScreen, "close"),
    operate(homeScreen, "countAll"),
  ],
);

export const nonModalChild = scenario(
  "Open the help, count all, and close the help; while helpPanel, which is not modal, is open, homeScreen still accepts the operation countAll and subscribes to taskCount again with all, and helpPanel accepts the operation closeHelp",
  [
    at("2026-10-25T10:00:00+09:00"),
    operate(homeScreen, "openHelp"),
    operate(homeScreen, "countAll"),
    operate(helpPanel, "closeHelp"),
  ],
);
