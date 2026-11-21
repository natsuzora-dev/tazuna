import { domain, explore } from "@natsuzora-dev/tazuna";
import { Task } from "./tasks.ts";

export const tasksExplore = explore({ service: "tasks", depth: 2, domains: [domain(Task.fields.id, ["a"])] });
