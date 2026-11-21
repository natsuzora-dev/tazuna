import { domain, explore } from "@natsuzora-dev/tazuna";
import { Note } from "./threads.ts";

export const threadsExplore = explore({
  service: "threads",
  depth: 2,
  domains: [domain(Note.fields.id, ["a"]), domain(Note.fields.text, ["a"])],
});
