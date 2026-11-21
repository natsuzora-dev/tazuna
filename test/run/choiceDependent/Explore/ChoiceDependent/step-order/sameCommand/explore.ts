import { domain, explore } from "@natsuzora-dev/tazuna";
import { set } from "./sameCommand.ts";

export const sameCommandExplore = explore({
  service: "sameCommand",
  depth: 2,
  domains: [domain(set.input.by, ["task-1", "task-2"])],
});
