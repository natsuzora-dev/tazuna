import { at, mock, receive, scenario, send } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { permission } from "./app.ts";

const unavailable = mock(permission, [
  device.requestPermission,
  { result: "rejected", rejection: { kind: "unavailable" } },
]);
const accepted = mock(permission, [device.requestPermission, { result: "accepted" }]);

export const grantAfterRetry = scenario("The user grants the permission that the app asked for again; no violation", [
  at("2026-10-25T09:00:00+09:00"),
  unavailable,
  accepted,
  receive(device.granted, {}, { resultOf: accepted }),
]);

export const askDevice = scenario(
  "Send the command of the device to the app; requestPermission is not a command of app, so test reports unownedTarget",
  [at("2026-10-25T09:00:00+09:00"), send(device.requestPermission, {})],
);
