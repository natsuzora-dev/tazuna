import { domain, explore } from "@natsuzora-dev/tazuna";
import { tag } from "./tags.ts";

export const tagsExplore = explore({ service: "tags", depth: 2, domains: [domain(tag.input.name, ["a"])] });
