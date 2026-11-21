import { domain, explore } from "@natsuzora-dev/tazuna";
import { Mark } from "./marks.ts";

export const marksExplore = explore({ service: "marks", depth: 2, domains: [domain(Mark.fields.id, ["a"])] });
