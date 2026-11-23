import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, machine, event, contract, scenario } = service({
  name: "countdown",
  description: "Count ticks",
});

export const ticked = event({});

export const tick = command({ callers: ["client"], emits: [ticked] }).decide(() => [emit(ticked, {})]);

export const countdown = machine({
  description: "Count down from one on every tick, entering counting again with the ticks left",
  receives: { ticked },
  initial: "running",
  states: { running: { initial: "counting", states: { counting: { held: { left: z.int().nonnegative() } } } } },
}).chart({
  states: {
    running: { initial: { with: { left: () => 1 } } },
    counting: {
      on: {
        ticked: [
          {
            guard: { someLeft: ({ held }) => held.left > 0 },
            target: "counting",
            reenter: true,
            with: { left: ({ held }) => held.left - 1 },
          },
        ],
      },
    },
  },
});

export const countdownContract = contract({ tick });
