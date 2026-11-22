import { parseInstant } from "@natsuzora-dev/tazuna";
import { scenario } from "./todo.ts";

export const start = scenario({
  description:
    "Start the service; the initial edge of running fills the task of watching, and its with throws because there is no task, so test reports exception of watcher",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (_w) => {},
  then: () => [],
});
