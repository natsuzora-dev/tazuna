import { at, mock, restart, scenario, send, subscribe, unsubscribe } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { ask, permission, status } from "./app.ts";

export const answerAfterRestart = scenario(
  "Press ask, restart, and answer requestPermission; the restart discards the request, and permission starts again in idle, so test reports missingWaitingRequest",
  [
    at("2026-10-25T10:00:00+09:00"),
    send(ask, {}),
    restart(),
    mock(permission, [device.requestPermission, { result: "accepted" }]),
  ],
);

const watching = subscribe(status, {});

export const unsubscribeAfterRestart = scenario(
  "Subscribe to status, restart, and end the subscription; the restart drops the subscription, so test reports unopenedSubscription",
  [at("2026-10-25T10:00:00+09:00"), watching, restart(), unsubscribe(watching)],
);
