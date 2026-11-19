import { any, none } from "@natsuzora-dev/tazuna";
import { screen } from "./data.ts";

export const editScreen = screen({
  description: "A screen that edits the title row and the completion row of a task at once",
  controls: { save: { label: "Save" } },
  initial: "editing",
  states: {
    editing: {
      type: "parallel",
      states: {
        title: { initial: "viewing", states: { viewing: {}, renaming: {} } },
        completion: { initial: "ready", states: { ready: {}, completing: {} } },
      },
    },
  },
}).chart({
  offers: { save: any },
  states: {
    viewing: { on: { save: [{ target: "renaming" }] } },
    renaming: { offers: { save: none }, on: { save: [{ target: "viewing" }] } },
    ready: { on: { save: [{ target: "completing" }] } },
    completing: { offers: { save: () => [{}] }, on: { save: [{ target: "ready" }] } },
  },
});
