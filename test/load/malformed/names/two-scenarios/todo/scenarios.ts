import { parseInstant } from "@natsuzora-dev/tazuna";
import { scenario } from "./todo.ts";

export const startsDay = scenario({
  description: "Start in the morning",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [] },
  when: () => {},
  then: () => [],
});
