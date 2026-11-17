import { service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { screen, scenario } = service({
  name: "fractionalCountOpener",
  description: "Pick a number, opening the picker with a fractional count",
});

export const pickScreen = screen({
  description: "Pick a number below a whole count",
  input: { count: z.number().int() },
  initial: "picking",
  states: { picking: {} },
}).chart({});

export const homeScreen = screen({
  description: "Open the picker",
  screens: { pickScreen },
  initial: "picking",
  states: { picking: {}, done: { type: "final" } },
}).chart({
  states: {
    picking: { opens: { pickScreen: { modal: true, input: () => ({ count: 0.5 }), onDone: [{ target: "done" }] } } },
  },
});
