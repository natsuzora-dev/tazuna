import { parseInstant } from "@natsuzora-dev/tazuna";
import { scenario } from "./screens.ts";

export const start = scenario({
  description:
    "Start the service; the initialContext of counterScreen returns the ISO text of an instant, which the integer schema of the context rejects, so test reports initialContextSchema",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [] },
  when: (_w) => {},
  then: () => [],
});
