import { scenario } from "./limits.ts";

export const start = scenario(
  "Start the service; the default limit 0 is below the minimum 1 of the context schema, so test reports initialContextSchema",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [] },
    when: (_w) => {},
    then: () => [],
  },
);
