import { domain, explore } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";

export const screensExplore = explore({
  service: "screens",
  depth: 2,
  domains: [domain(todo.notesIn.output.count, [0]), domain(todo.notesNamed.output.count, [0])],
});
