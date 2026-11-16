import { at, scenario } from "@natsuzora-dev/tazuna";

export const start = scenario("Start the service; pickScreen closes with a number below the count; no violation", [
  at("2026-10-25T09:00:00+09:00"),
]);
