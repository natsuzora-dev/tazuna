import { scenario, start } from "./sameCommand.ts";

export const startOnce = scenario(
  "Start; pinger sends ping as first and as second with equal input, and the answer taken first decides the flag, so test reports stepOrder",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: { Flag: { by: "" } }, peers: [] },
    when: (w) => {
      w.client.send(start, {});
    },
    then: () => [],
  },
);
