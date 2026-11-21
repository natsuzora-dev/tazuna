import { domain, explore } from "@natsuzora-dev/tazuna";
import { Task } from "./watcher.ts";

export const watcherExplore = explore({
  service: "watcher",
  depth: 2,
  domains: [domain(Task.fields.id, ["task-1"]), domain(Task.fields.title, ["Buy milk"])],
});
