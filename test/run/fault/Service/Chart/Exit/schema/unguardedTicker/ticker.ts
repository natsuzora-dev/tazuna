import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, machine, event, contract, scenario } = service({
  name: "unguardedTicker",
  description: "Count ticks without a guard on the countdown",
});

export const ticked = event({});

export const tick = command({ callers: ["client"], emits: [ticked] }).decide(() => [emit(ticked, {})]);

export const countdown = machine({
  description: "Count down from one on every tick",
  context: { left: z.int().nonnegative().default(1) },
  receives: { ticked },
  initial: "counting",
  states: { counting: {} },
}).chart({ states: { counting: { on: { ticked: [{ assign: { left: ({ context }) => context.left - 1 } }] } } } });

export const unguardedTicker = contract({ tick });
