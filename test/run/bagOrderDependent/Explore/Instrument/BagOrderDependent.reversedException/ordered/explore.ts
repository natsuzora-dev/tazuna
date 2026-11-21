import { domain, explore } from "@natsuzora-dev/tazuna";
import { Task } from "./ordered.ts";

export const orderedExplore = explore({ service: "ordered", depth: 2, domains: [domain(Task.fields.id, ["task-1"])] });
