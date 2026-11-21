import { domain, explore } from "@natsuzora-dev/tazuna";
import { post } from "./tags.ts";

export const tagsExplore = explore({
  service: "tags",
  depth: 2,
  domains: [domain(post.input.id, ["a"]), domain(post.input.text, ["a"])],
});
