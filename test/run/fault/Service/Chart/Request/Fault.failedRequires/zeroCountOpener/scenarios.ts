import { scenario } from "./opener.ts";

export const start = scenario({
  description:
    "Start the service; homeScreen opens pickScreen with count 0, which fails the requires positive of pickScreen, so test reports failedRequires",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [] },
  when: (_w) => {},
  then: () => [],
});
