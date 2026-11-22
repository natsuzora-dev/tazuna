import { domain, explore } from "@natsuzora-dev/tazuna";
import { addItem } from "./todo.ts";

export const todoExplore = explore({
  service: "todo",
  depth: 2,
  domains: [domain(addItem.input.note, ["milk"]), domain(addItem.input.qty, [5])],
});
