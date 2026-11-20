import { datetime, service } from "@natsuzora-dev/tazuna";

export const { screen, scenario } = service({
  name: "counters",
  description: "Open a counter from a stored start time",
});

const stored: Temporal.Instant = JSON.parse('"2026-10-25T00:00:00Z"');

export const counterScreen = screen({
  description: "Count up from the stored start time",
  context: { since: datetime },
  initial: "counting",
  states: { counting: {} },
}).chart({ initialContext: () => ({ since: stored }) });

export const homeScreen = screen({
  description: "Open the counter",
  screens: { counterScreen },
  initial: "opening",
  states: { opening: {}, done: { type: "final" } },
}).chart({
  states: { opening: { opens: { counterScreen: { modal: true, onDone: [{ target: "done" }] } } } },
});
