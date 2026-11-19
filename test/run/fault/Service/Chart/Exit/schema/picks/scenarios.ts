import { scenario } from "./picks.ts";

export const start = scenario(
  "Start the service; the set picked holds the element a twice, so test reports contextSchema",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [] },
    when: (_w) => {},
    then: () => [],
  },
);
