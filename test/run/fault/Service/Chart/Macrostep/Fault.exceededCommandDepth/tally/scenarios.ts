import { scenario } from "./tally.ts";

export const start = scenario({
  description: "Start the service; counter counts to three and stops, because its guards stop the chain; no violation",
  given: { start: "2026-10-25T09:00:00+09:00", records: { Counter: { value: 0 } }, peers: [] },
  when: (_w) => {},
  then: () => [],
});
