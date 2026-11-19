import { scenario } from "./sender.ts";

export const start = scenario({
  description:
    "Start the service; greeter sends greet with an empty name, which fails the input schema of greet, so test reports inputSchema of greeter",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [] },
  when: (_w) => {},
  then: () => [],
});
