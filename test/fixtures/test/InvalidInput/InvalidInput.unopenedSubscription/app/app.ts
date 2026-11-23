import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { device } from "../device/contract.ts";

export const { command, query, machine, event, contract, scenario } = service({
  name: "app",
  description: "Use the device",
});

export const askPressed = event({});

export const ask = command({ callers: ["client"], emits: [askPressed] }).decide(() => [emit(askPressed, {})]);

export const status = query({ callers: ["client"], output: { ready: z.boolean() } }).resolve(() => ({ ready: true }));

export const permission = machine({
  description: "Ask for the permission when ask is pressed",
  receives: { askPressed },
  commands: { requestPermission: device.requestPermission },
  initial: "idle",
  states: { idle: {}, asking: {} },
}).chart({
  states: {
    idle: { on: { askPressed: [{ target: "asking" }] } },
    asking: { sends: { requestPermission: { onAccepted: [{ target: "idle" }], onRejected: [] } } },
  },
});
