import { domain, explore } from "@natsuzora-dev/tazuna";
import { addTask } from "./echo.ts";

export const echoExplore = explore({ service: "echo", depth: 2, domains: [domain(addTask.input.taskId, ["task-1"])] });
