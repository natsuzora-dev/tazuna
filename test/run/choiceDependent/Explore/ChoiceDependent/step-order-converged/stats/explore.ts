import { domain, explore } from "@natsuzora-dev/tazuna";
import { Task } from "./stats.ts";

export const statsExplore = explore({
  service: "stats",
  depth: 2,
  domains: [domain(Task.fields.id, ["task-1"]), domain(Task.fields.title, ["Buy milk"])],
});
