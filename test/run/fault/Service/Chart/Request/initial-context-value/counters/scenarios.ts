import { parseInstant } from "@natsuzora-dev/tazuna";
import { scenario } from "./screens.ts";

export const start = scenario({
  description:
    "Start the service; the initialContext of counterScreen returns null, which is no object, so test reports initialContextSchema as Lean does instead of failing to merge it with the defaults",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [] },
  when: (_w) => {},
  then: () => [],
});
