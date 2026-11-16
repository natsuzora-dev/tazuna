import { scenario } from "./chains.ts";

export const start = scenario(
  "Start the service; 101 chains of 100 pings send more than 10000 commands in the start message, though no chain is longer than 100, so test reports exceededMessageCommands",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: {} },
    when: (_w) => {},
    then: () => [],
  },
);
