import { domain, explore } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";

export const emptyPrefixScreensExplore = explore({
  service: "emptyPrefixScreens",
  depth: 2,
  domains: [domain(todo.titled.output.titles, [[]])],
});
