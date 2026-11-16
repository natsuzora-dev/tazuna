import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { countCompleted, resetCount, resumeCounting } from "./stats.ts";

export const countsOne = scenario("Count a completed task; no violation", [
  at("2026-10-25T09:00:00+09:00"),
  send(countCompleted, {}),
]);

export const resumesOnce = scenario("Resume counting completed tasks; no violation", [
  at("2026-10-25T09:00:00+09:00"),
  send(resumeCounting, {}),
]);

export const resetCountOnce = scenario("Reset the count of completed tasks; no violation", [
  at("2026-10-25T09:00:00+09:00"),
  send(resetCount, {}),
]);
