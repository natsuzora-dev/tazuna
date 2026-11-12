import { at, operate, scenario } from "@natsuzora-dev/tazuna";
import { taskListScreen } from "./screens.ts";

export const filterAndClose = scenario("Filter the list and close it; no violation", [
  at("2026-10-25T00:00:00Z"),
  operate(taskListScreen, "filter", { prefix: "Buy" }),
  operate(taskListScreen, "close"),
]);

export const filterAndCloseWrongSubscriptions = scenario(
  "Same inputs as filterAndClose; the implementation trace of this scenario opens the first subscription with another input and an extra subscription at the end, so verify reports unopenedSubscription and unexpectedSubscription",
  [at("2026-10-25T00:00:00Z"), operate(taskListScreen, "filter", { prefix: "Buy" }), operate(taskListScreen, "close")],
);
