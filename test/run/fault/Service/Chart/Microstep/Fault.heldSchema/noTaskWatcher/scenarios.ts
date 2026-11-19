import { scenario } from "./watcher.ts";

export const start = scenario({
  description:
    "Start the service; the initial edge of running fills the task of watching while no task exists, so the task does not match its schema, so test reports heldSchema",
  given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: [] },
  when: (_w) => {},
  then: () => [],
});
