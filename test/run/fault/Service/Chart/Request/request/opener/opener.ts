import { service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { screen, scenario } = service({ name: "opener", description: "Pick a number" });

export const pickScreen = screen({
  description: "Pick a number below a positive count",
  input: { count: z.int() },
  initial: "picking",
  states: { picking: {} },
  requires: { positive: ({ input }) => input.count > 0 },
}).chart({});

export const homeScreen = screen({
  description: "Open the picker",
  screens: { pickScreen },
  initial: "picking",
  states: { picking: {}, done: { type: "final" } },
}).chart({
  states: {
    picking: { opens: { pickScreen: { modal: true, input: () => ({ count: 1 }), onDone: [{ target: "done" }] } } },
  },
});
