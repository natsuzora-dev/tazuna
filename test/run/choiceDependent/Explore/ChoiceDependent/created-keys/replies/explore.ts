import { domain, explore } from "@natsuzora-dev/tazuna";
import { post } from "./replies.ts";

export const repliesExplore = explore({
  service: "replies",
  depth: 2,
  domains: [domain(post.input.id, ["a"]), domain(post.input.text, ["a"])],
});
