import { bag, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { screen, scenario } = service({
  name: "throwingRequires",
  description: "Open a picker whose requires faults on points that sum to no safe integer",
});

export const pickScreen = screen({
  description: "Pick a number below the positive total of the points",
  input: { points: bag(z.int()) },
  initial: "picking",
  states: { picking: {} },
  requires: { positive: ({ input }) => input.points.sum((p) => p) > 0 },
}).chart({});

export const homeScreen = screen({
  description: "Open the picker",
  screens: { pickScreen },
  initial: "picking",
  states: { picking: {}, done: { type: "final" } },
}).chart({
  states: {
    picking: {
      opens: {
        pickScreen: {
          modal: true,
          input: () => ({ points: [5_000_000_000_000_000, 5_000_000_000_000_000] }),
          onDone: [{ target: "done" }],
        },
      },
    },
  },
});
