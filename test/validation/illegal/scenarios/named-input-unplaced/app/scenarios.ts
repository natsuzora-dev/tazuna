import { at, mock, receive, scenario } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { permission } from "./app.ts";

const accepted = mock(permission, [device.requestPermission, { result: "accepted" }]);

export const grantBeforeAnswer = scenario(
  "Receive a result before the answer that it is linked to; check reports namedInputUnplaced",
  [at("2026-10-25T09:00:00+09:00"), receive(device.granted, {}, { resultOf: accepted }), accepted],
);

export const answer = scenario("Answer the request", [at("2026-10-25T09:00:00+09:00"), accepted]);

export const grantFromAnotherScenario = scenario(
  "Link a result to a mock that only the scenario answer places; check reports namedInputUnplaced",
  [at("2026-10-25T09:00:00+09:00"), receive(device.granted, {}, { resultOf: accepted })],
);
