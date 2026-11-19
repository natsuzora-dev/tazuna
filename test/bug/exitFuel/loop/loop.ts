import { any, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { screen, scenario } = service({ name: "loop", description: "Open screens 10 deep" });

export const selfScreen: any = screen({
  description: "A screen that opens itself until depth 10",
  input: { depth: z.number() },
  screens: {
    get selfScreen() {
      return selfScreen;
    },
  },
  initial: "check",
  states: { check: {}, open: {}, leaf: {} },
}).chart({
  states: {
    check: {
      always: [{ guard: { deeper: ({ input }: any) => input.depth < 10 }, target: "open" }, { target: "leaf" }],
    },
    open: {
      opens: { selfScreen: { modal: false, input: ({ input }: any) => ({ depth: input.depth + 1 }), onDone: [] } },
    },
  },
});

export const homeScreen = screen({
  description: "Open the self screen",
  screens: { selfScreen },
  controls: { close: { label: "Close" } },
  initial: "opening",
  states: { opening: {}, closed: { type: "final" } },
}).chart({
  offers: { close: any },
  states: {
    opening: {
      opens: { selfScreen: { modal: false, input: () => ({ depth: 1 }), onDone: [] } },
      on: { close: [{ target: "closed" }] },
    },
  },
});
