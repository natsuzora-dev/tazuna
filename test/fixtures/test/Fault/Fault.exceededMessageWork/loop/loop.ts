import { service } from "@natsuzora-dev/tazuna";

export const { screen, scenario } = service({ name: "loop", description: "Open a screen forever" });

export const doneScreen = screen({
  description: "A screen that is done at once",
  initial: "closed",
  states: { closed: { type: "final" } },
}).chart({});

export const homeScreen = screen({
  description: "Open the done screen again whenever it is done",
  screens: { doneScreen },
  initial: "opening",
  states: { opening: {} },
}).chart({
  states: { opening: { opens: { doneScreen: { modal: true, onDone: [{ target: "opening", reenter: true }] } } } },
});
