import { contract, emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, machine, event } = service({ description: "Count ticks without a guard on the countdown" });

export const ticked = event({});

export const tick = command({ emits: [ticked] }).decide(() => [emit(ticked, {})]);

export const countdown = machine({
  description: "Count down from one on every tick, and hold the ticks left while counting",
  context: { left: z.number().default(1) },
  receives: { ticked },
  initial: "counting",
  states: { counting: { held: { left: z.number().nonnegative() } } },
}).chart({
  states: {
    counting: {
      holds: { left: ({ context }) => context.left },
      on: { ticked: [{ assign: { left: ({ context }) => context.left - 1 } }] },
    },
  },
});

export const unguardedCountdown = contract({ tick });
