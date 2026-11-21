import { domain, explore } from "@natsuzora-dev/tazuna";
import { addTasks } from "./count.ts";

export const countExplore = explore({
  service: "count",
  depth: 2,
  domains: [domain(addTasks.input.taskIds, [["a", "b"]])],
});
