import { domain, explore } from "@natsuzora-dev/tazuna";
import { addTask } from "./todo.ts";

export const todoExplore = explore({ service: "todo", depth: 2, domains: [domain(addTask.input.taskId, ["task-1"])] });
