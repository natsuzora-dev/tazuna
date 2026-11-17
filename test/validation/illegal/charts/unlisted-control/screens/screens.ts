import { any, service, unchecked } from "@natsuzora-dev/tazuna";

export const { screen, contract } = service({ name: "screens", description: "Show a list" });

export const listScreen = screen({
  description: "A list whose own offers leave out the control close",
  controls: { refresh: { label: "Refresh" }, close: { label: "Close" } },
  initial: "shown",
  states: { shown: {}, closed: { type: "final" } },
}).chart({
  offers: unchecked({ refresh: any }),
  states: { shown: { on: { refresh: [], close: [{ target: "closed" }] } } },
});
