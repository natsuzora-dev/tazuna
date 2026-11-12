import { at, mock, receive, scenario } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { permission } from "./app.ts";

const unavailable = mock(permission, [
  device.requestPermission,
  { result: "rejected", rejection: { kind: "unavailable" } },
]);
const accepted = mock(permission, [device.requestPermission, { result: "accepted" }]);
const acceptedAgain = mock(permission, [device.requestPermission, { result: "accepted" }]);

export const grantAfterRetry = scenario(
  "Link results to a rejected request and to a request that cannot have them; test reports resultOfUnacceptedRequest and resultOfUnlistedEvent",
  [
    at("2026-10-25T09:00:00+09:00"),
    unavailable,
    receive(device.granted, {}, { resultOf: unavailable }),
    accepted,
    receive(device.denied, {}, { resultOf: accepted }),
  ],
);

export const grantAfterExtraAnswer = scenario(
  "Link a result to a mock that comes after the request is answered; test reports noWaitingRequest",
  [at("2026-10-25T09:00:00+09:00"), accepted, acceptedAgain, receive(device.granted, {}, { resultOf: acceptedAgain })],
);
