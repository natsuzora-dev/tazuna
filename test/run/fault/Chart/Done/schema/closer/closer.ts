import { service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { screen } = service({ description: "Close a screen" });

export const doneScreen = screen({
  description: "A screen that closes with a negative count",
  output: { count: z.number().nonnegative() },
  controls: { close: { label: "Close" } },
  initial: "open",
  states: { open: {}, closed: { type: "final" } },
}).chart({ resolve: () => ({ count: -1 }), states: { open: { on: { close: [{ target: "closed" }] } } } });

export const homeScreen = screen({
  description: "Open the done screen, then show the count",
  screens: { doneScreen },
  initial: "opening",
  states: { opening: {}, shown: { type: "final" } },
}).chart({ states: { opening: { opens: { doneScreen: { modal: true, onDone: [{ target: "shown" }] } } } } });
