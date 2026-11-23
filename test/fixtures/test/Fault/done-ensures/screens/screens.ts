import { service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { screen, scenario } = service({ name: "screens", description: "Pick a number" });

export const pickScreen = screen({
  description: "Pick a number",
  input: { count: z.int() },
  output: { picked: z.int() },
  initial: "picked",
  states: { picked: { type: "final" } },
  ensures: { belowCount: ({ input, output }) => output.picked < input.count },
}).chart({ resolve: ({ input }) => ({ picked: input.count - 1 }) });

export const listScreen = screen({
  description: "Pick a number, then list the tasks",
  screens: { pickScreen },
  initial: "picking",
  states: { picking: {}, listing: { type: "final" } },
}).chart({
  states: {
    picking: { opens: { pickScreen: { modal: true, input: () => ({ count: 2 }), onDone: [{ target: "listing" }] } } },
  },
});
