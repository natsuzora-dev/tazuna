import { scenario } from "./screens.ts";

export const start = scenario({
  description:
    "Start the service; homeScreen opens counterScreen from -1, and the refinement of the context schema of counterScreen throws, so test reports exception of counterScreen",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [] },
  when: (_w) => {},
  then: () => [],
});
