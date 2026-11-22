import { parseInstant } from "@natsuzora-dev/tazuna";
import { arm, scenario, taskIds } from "./tasks.ts";

export const subscribed = scenario({
  description:
    "Subscribe to taskIds and arm at 11:00; the deadlines of first and second tie. They add different tasks, but the answer after the first deadline's message shows which clock rang first, so test reports stepOrder",
  given: { start: parseInstant("2026-10-25T11:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.subscribe(taskIds, {});
    w.client.send(arm, {});
  },
  then: () => [],
});
