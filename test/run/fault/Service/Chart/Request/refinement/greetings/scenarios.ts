import { scenario } from "./greetings.ts";

export const start = scenario(
  "Start the service; greeter sends greet with an empty name, and the refinement of the input schema of greet throws, so test reports exception of greet",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: {} },
    when: (_w) => {},
    then: () => [],
  },
);
