import { parseInstant } from "@natsuzora-dev/tazuna";
import { closeTasks, scenario } from "./closer.ts";

export const closeOnce = scenario({
  description:
    "Close the tasks; each machine assigns notes in two regions or copies in one microstep, which have no order, so test reports bothAssign",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [] },
  when: (w) => {
    w.client.as("client").send(closeTasks, {});
  },
  then: () => [],
});
