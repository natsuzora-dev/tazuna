import { domain, explore } from "@natsuzora-dev/tazuna";
import { Task } from "./plain.ts";

export const plainExplore = explore({
  service: "plain",
  depth: 2,
  domains: [domain(Task.fields.id, ["a"]), domain(Task.fields.text, ["a"])],
});
