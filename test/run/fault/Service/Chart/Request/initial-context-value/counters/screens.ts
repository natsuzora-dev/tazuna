import { service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { screen, scenario } = service({ name: "counters", description: "Open a counter from a stored start" });

const stored: { readonly count: number } = JSON.parse("null");

export const counterScreen = screen({
  description: "Count up from the stored start",
  context: { count: z.number() },
  initial: "counting",
  states: { counting: {} },
}).chart({ initialContext: () => stored });

export const homeScreen = screen({
  description: "Open the counter",
  screens: { counterScreen },
  initial: "opening",
  states: { opening: {}, done: { type: "final" } },
}).chart({
  states: { opening: { opens: { counterScreen: { modal: true, onDone: [{ target: "done" }] } } } },
});
