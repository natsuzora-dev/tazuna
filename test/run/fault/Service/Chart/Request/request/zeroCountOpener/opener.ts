import { service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { screen } = service({ description: "Pick a number, opening the picker with count 0" });

export const pickScreen = screen({
  description: "Pick a number below a positive count",
  input: { count: z.number() },
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
    picking: { opens: { pickScreen: { modal: true, input: () => ({ count: 0 }), onDone: [{ target: "done" }] } } },
  },
});
