import { at, scenario } from "@natsuzora-dev/tazuna";

export const start = scenario(
  "Start the service; watcher starts in watching with no task, so the held task does not match its schema, so test reports heldSchema",
  [at("2026-10-25T09:00:00+09:00")],
);
