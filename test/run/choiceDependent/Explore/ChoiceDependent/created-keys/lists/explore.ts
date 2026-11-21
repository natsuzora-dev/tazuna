import { domain, explore } from "@natsuzora-dev/tazuna";
import { post } from "./lists.ts";

export const listsExplore = explore({
  service: "lists",
  depth: 2,
  domains: [domain(post.input.id, ["a"]), domain(post.input.text, ["a"])],
});
