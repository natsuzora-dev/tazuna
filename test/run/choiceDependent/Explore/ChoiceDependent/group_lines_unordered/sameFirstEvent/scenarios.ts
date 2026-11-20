import { scenario, start } from "./sameFirstEvent.ts";

export const startOnce = scenario({
  description:
    "Start; addTwo and addThree each emit task-1 before their second event, and counter counts the task-1 events before task-3, so test reports stepOrder",
  given: { start: "2026-10-25T09:00:00+09:00", records: { Count: { seen: 0 } }, peers: [] },
  when: (w) => {
    w.client.send(start, {});
  },
  then: () => [],
});
