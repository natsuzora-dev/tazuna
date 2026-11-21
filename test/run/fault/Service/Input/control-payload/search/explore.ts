import { domain, explore } from "@natsuzora-dev/tazuna";
import { searchScreen } from "./search.ts";

export const searchExplore = explore({
  service: "search",
  depth: 2,
  domains: [domain(searchScreen.controls.search.payload.query, [])],
});
