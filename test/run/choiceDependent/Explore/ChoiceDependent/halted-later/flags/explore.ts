import { domain, explore } from "@natsuzora-dev/tazuna";
import { addTask } from "./flags.ts";

export const flagsExplore = explore({
  service: "flags",
  depth: 2,
  domains: [domain(addTask.input.taskId, ["task-1"])],
});
