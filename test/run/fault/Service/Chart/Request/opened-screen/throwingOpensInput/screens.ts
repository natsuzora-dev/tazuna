import { service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { screen, scenario } = service({ description: "Open a picker with an input that throws" });

export const pickScreen = screen({
  description: "Pick a number below the count",
  input: { count: z.number() },
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
    picking: {
      opens: {
        pickScreen: {
          modal: true,
          input: () => {
            throw new Error("there is no count yet");
          },
          onDone: [{ target: "done" }],
        },
      },
    },
  },
});
