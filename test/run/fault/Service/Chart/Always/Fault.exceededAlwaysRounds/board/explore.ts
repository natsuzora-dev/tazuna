import { domain, explore } from "@natsuzora-dev/tazuna";
import { Task } from "./board.ts";

export const boardExplore = explore({
  service: "board",
  depth: 2,
  domains: [domain(Task.fields.id, ["a"]), domain(Task.fields.title, ["a"])],
});
