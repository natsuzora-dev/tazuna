import { parseInstant } from "@natsuzora-dev/tazuna";
import { scenario } from "./todo.ts";

export const dayLater = scenario({
  description:
    "Start the service and come back a day later; more than 1000 minutes have passed, so test reports exceededDueDeadlines",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [] },
  when: (w) => {
    w.clock.at(parseInstant("2026-10-26T09:00:00+09:00"));
  },
  then: () => [],
});
