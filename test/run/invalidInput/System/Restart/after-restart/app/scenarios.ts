import { at, mock, restart, scenario, send, subscribe, unsubscribe } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { ask, permission, status } from "./app.ts";

export const answerAfterRestart = scenario(
  "Press ask, restart, and answer requestPermission; the restart discards the request, and permission starts again in idle, so test reports noWaitingRequest",
  [
    at("2026-10-25T10:00:00+09:00"),
    send(ask, {}),
    restart(),
    mock(permission, [device.requestPermission, { result: "accepted" }]),
  ],
);

export const unsubscribeAfterRestart = scenario(
  "Subscribe to status with the id s1, restart, and end s1; the restart drops the subscription, so test reports subscriptionNotOpen",
  [at("2026-10-25T10:00:00+09:00"), subscribe(status, {}, { id: "s1" }), restart(), unsubscribe("s1")],
);
