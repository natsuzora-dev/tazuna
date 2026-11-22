import { parseInstant } from "@natsuzora-dev/tazuna";
import { scenario } from "../todo.ts";

export const startsDay = scenario({
  description: "Start at noon",
  given: { start: parseInstant("2026-10-25T12:00:00+09:00"), records: {}, peers: [] },
  when: () => {},
  then: () => [],
});
