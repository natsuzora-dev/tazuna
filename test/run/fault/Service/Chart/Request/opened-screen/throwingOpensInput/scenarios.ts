import { parseInstant } from "@natsuzora-dev/tazuna";
import { scenario } from "./screens.ts";

export const start = scenario({
  description:
    "Start the service; the opens input of homeScreen for pickScreen throws, so test reports exception of homeScreen",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [] },
  when: (_w) => {},
  then: () => [],
});
