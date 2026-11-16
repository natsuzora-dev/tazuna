import { at, mock, receive, scenario } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { permission } from "./app.ts";

const accepted = mock(permission, [device.requestPermission, { result: "accepted" }]);

export const resultRedelivered = scenario(
  "Accept the permission request and receive device.granted twice with the id g1 and the same resultOf; app writes the second as a line with resultOf and does not process it",
  [
    at("2026-10-25T09:00:00+09:00"),
    accepted,
    receive(device.granted, {}, { id: "g1", resultOf: accepted }),
    receive(device.granted, {}, { id: "g1", resultOf: accepted }),
  ],
);
