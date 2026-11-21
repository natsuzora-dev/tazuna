import { domain, explore } from "@natsuzora-dev/tazuna";
import { Task } from "./cleanup.ts";

export const cleanupExplore = explore({
  service: "cleanup",
  depth: 2,
  domains: [domain(Task.fields.id, ["task-1"]), domain(Task.fields.title, ["Buy milk"])],
});
