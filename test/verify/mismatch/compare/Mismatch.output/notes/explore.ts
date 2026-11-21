import { domain, explore } from "@natsuzora-dev/tazuna";
import { post } from "./notes.ts";

export const notesExplore = explore({
  service: "notes",
  depth: 2,
  domains: [domain(post.input.id, ["a"]), domain(post.input.text, ["a"])],
});
