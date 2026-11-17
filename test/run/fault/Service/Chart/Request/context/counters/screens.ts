import { service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { screen, scenario } = service({ name: "counters", description: "Open a counter from a negative start" });

export const counterScreen = screen({
  description: "Count up from the given start",
  input: { start: z.number() },
  context: {
    count: z.number().refine((count) => {
      if (count < 0) throw new Error("a count cannot start below zero");
      return true;
    }),
  },
  initial: "counting",
  states: { counting: {} },
}).chart({ initialContext: ({ input }) => ({ count: input.start }) });

export const homeScreen = screen({
  description: "Open the counter",
  screens: { counterScreen },
  initial: "opening",
  states: { opening: {}, done: { type: "final" } },
}).chart({
  states: {
    opening: {
      opens: { counterScreen: { modal: true, input: () => ({ start: -1 }), onDone: [{ target: "done" }] } },
    },
  },
});
