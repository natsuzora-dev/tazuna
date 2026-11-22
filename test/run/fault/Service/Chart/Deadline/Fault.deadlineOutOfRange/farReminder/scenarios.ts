import { parseInstant } from "@natsuzora-dev/tazuna";
import { scenario } from "./farReminder.ts";

export const start = scenario({
  description:
    "Start the service; the deadline far would be due past the year 9999, so test reports deadlineOutOfRange",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [] },
  when: (_w) => {},
  then: () => [],
});
