import { scenario, tick } from "./counter.ts";

export const tickOnce = scenario(
  "Tick once; five automations each bump the counter from the count they read, so the five bumps can run in 120 orders, all ending at 5, and the search stops at 64 orders and reports searchLimit",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: { Counter: { count: 0 } }, peers: [] },
    when: (w) => {
      w.client.send(tick, {});
    },
    then: () => [],
  },
);
