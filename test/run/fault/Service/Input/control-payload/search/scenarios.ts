import { parseInstant } from "@natsuzora-dev/tazuna";
import { scenario, searchScreen } from "./search.ts";

export const searchEmpty = scenario({
  description:
    "Search with an empty query; the refinement of the payload schema of search throws, so test reports exception of searchScreen",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [] },
  when: (w) => {
    w.user.operate(w.startup.screen(searchScreen), "search", { query: "" });
  },
  then: () => [],
});
