import { scenario } from "./counters.ts";

export const start = scenario("Start the service; the copy sets visits to 0, so test reports copyContextSchema", {
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [] },
  when: (_w) => {},
  then: () => [],
});
