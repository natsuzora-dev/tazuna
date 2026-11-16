import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { tick } from "./ticker.ts";

export const tickTwice = scenario(
  "Tick twice; without a guard, countdown counts below zero, which its context schema rejects, so test reports contextSchema",
  [at("2026-10-25T09:00:00+09:00"), send(tick, {}), send(tick, {})],
);
