import { at, operate, scenario, unchecked } from "@natsuzora-dev/tazuna";
import { counterScreen } from "./screens.ts";

export const setCount = scenario("Set the count; no violation", [
  at("2026-10-25T09:00:00+09:00"),
  operate(counterScreen, "countSet", { count: 3 }),
]);

export const setCountToText = scenario(
  "Set the count to a text; the payload schema of countSet rejects it, so test reports controlPayloadSchema",
  [at("2026-10-25T09:00:00+09:00"), operate(counterScreen, "countSet", { count: unchecked("three") })],
);
