import { at, operate, scenario } from "@natsuzora-dev/tazuna";
import { doneScreen } from "./closer.ts";

export const closeDone = scenario("Close the done screen; test reports screenOutputSchema", [
  at("2026-10-25T09:00:00+09:00"),
  operate(doneScreen, "close"),
]);
