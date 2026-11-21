import { domain, explore } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";

export const screensExplore = explore({
  service: "screens",
  depth: 2,
  domains: [domain(todo.linked.output.count, [0])],
});
