import { scenario } from "./watcher.ts";

export const start = scenario("Start the service; no violation", {
  given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: [] },
  when: (_w) => {},
  then: () => [],
});
