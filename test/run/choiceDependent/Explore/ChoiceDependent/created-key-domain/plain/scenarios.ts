import { parseInstant } from "@natsuzora-dev/tazuna";
import { arm, scenario, taskIds } from "./plain.ts";

export const subscribed = scenario({
  description:
    "Subscribe to taskIds, whose ids have the schema of the key field Task.fields.id, and arm at 11:00; the deadlines of first and second tie and each create a task. Both orders answer the first created key first, but under that key the records hold a different text, so test reports stepOrder",
  given: { start: parseInstant("2026-10-25T11:00:00+09:00"), records: { Task: [], Count: { n: 0 } }, peers: [] },
  when: (w) => {
    w.client.as("client").subscribe(taskIds, {});
    w.client.as("client").send(arm, {});
  },
  then: () => [],
});
