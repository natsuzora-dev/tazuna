import { domain, explore } from "@natsuzora-dev/tazuna";
import { Task } from "./typed.ts";

export const typedExplore = explore({
  service: "typed",
  depth: 2,
  domains: [domain(Task.fields.id, ["a"]), domain(Task.fields.text, ["a"])],
});
