import { at, mock, receive, scenario } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { permission } from "./app.ts";

const unavailable = mock(permission, [
  device.requestPermission,
  { result: "rejected", rejection: { kind: "unavailable" } },
]);
const accepted = mock(permission, [device.requestPermission, { result: "accepted" }]);

export const grantAfterRetries = scenario(
  "Link a result to a mock that answers two requests; check reports resultOfPlacedTwice",
  [
    at("2026-10-25T09:00:00+09:00"),
    unavailable,
    unavailable,
    accepted,
    receive(device.granted, {}, { resultOf: unavailable }),
  ],
);
