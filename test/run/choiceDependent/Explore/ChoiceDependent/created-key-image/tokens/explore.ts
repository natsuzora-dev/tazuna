import { domain, explore } from "@natsuzora-dev/tazuna";
import { Note } from "./tokens.ts";

export const tokensExplore = explore({ service: "tokens", depth: 2, domains: [domain(Note.fields.id, ["a"])] });
