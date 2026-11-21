import { domain, explore } from "@natsuzora-dev/tazuna";
import { dueTasks } from "../dueTasks/tasks.ts";

export const stampedBoardExplore = explore({
  service: "stampedBoard",
  depth: 2,
  domains: [domain(dueTasks.dueBy.output.count, [0])],
});
