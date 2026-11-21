import { domain, explore } from "@natsuzora-dev/tazuna";
import { Task } from "./watcher.ts";

export const noTaskWatcherExplore = explore({
  service: "noTaskWatcher",
  depth: 2,
  domains: [domain(Task.fields.id, ["task-1"]), domain(Task.fields.title, ["task-1"])],
});
