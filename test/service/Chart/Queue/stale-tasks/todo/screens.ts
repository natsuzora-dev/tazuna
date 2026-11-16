import { screen, taskDropped } from "./todo.ts";

export const pickScreen = screen({
  description: "A screen that picks a task. It closes when a task is dropped",
  receives: { taskDropped },
  controls: { pick: { label: "Pick" } },
  initial: "picking",
  states: { picking: {}, picked: { type: "final" } },
}).chart({
  states: { picking: { on: { pick: [{ target: "picked" }], taskDropped: [{ target: "picked" }] } } },
});

export const homeScreen = screen({
  description: "A home screen that opens the pick screen and closes it when a task is dropped",
  receives: { taskDropped },
  screens: { pick: pickScreen },
  controls: { openPick: { label: "Open picker" } },
  initial: "home",
  states: { home: {}, picking: {} },
}).chart({
  states: {
    home: { on: { openPick: [{ target: "picking" }] } },
    picking: {
      on: { taskDropped: [{ target: "home" }] },
      opens: { pick: { modal: true, onDone: [{ target: "home" }] } },
    },
  },
});
