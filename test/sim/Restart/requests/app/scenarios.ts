import { at, mock, restart, scenario } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { permission } from "./app.ts";

const accepted = mock(permission, [device.requestPermission, { result: "accepted" }]);

export const firstRestart = scenario(
  "Restart as the first input; the service begins once, so permission sends one requestPermission, after the restart line",
  [at("2026-10-25T10:00:00+09:00"), restart()],
);

export const requestsDiscarded = scenario(
  "Begin at 10:00, restart at 10:05, and answer requestPermission; the restart discards the request of the first start, so the answer goes to the request of the new start",
  [at("2026-10-25T10:00:00+09:00"), at("2026-10-25T10:05:00+09:00"), restart(), accepted],
);
