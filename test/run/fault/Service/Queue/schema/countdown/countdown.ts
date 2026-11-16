import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, machine, event, contract, scenario } = service({ description: "Count ticks" });

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
      on: {
        ticked: [
          {
            guard: { someLeft: ({ context }) => context.left > 0 },
            assign: { left: ({ context }) => context.left - 1 },
          },
        ],
      },
    },
  },
});

export const countdownContract = contract({ tick });
