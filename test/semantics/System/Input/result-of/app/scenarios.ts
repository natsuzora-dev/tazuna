import { at, mock, receive, scenario } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { permission } from "./app.ts";

const accepted = mock(permission, [device.requestPermission, { result: "accepted" }]);

export const grant = scenario(
  "Accept the permission request and receive granted with its resultOf; device accepts the requestPermission that permission sends and emits the result event granted. The granted line of the snapshot has the id of the requestPermission request in resultOf",
  [at("2026-10-25T09:00:00+09:00"), accepted, receive(device.granted, {}, { resultOf: accepted })],
);
