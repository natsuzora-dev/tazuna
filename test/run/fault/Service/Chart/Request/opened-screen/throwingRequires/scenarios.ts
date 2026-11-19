import { scenario } from "./screens.ts";

export const start = scenario({
  description:
    "Start the service; homeScreen opens pickScreen with count 0, and the requires positive of pickScreen throws, so test reports exception of pickScreen",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [] },
  when: (_w) => {},
  then: () => [],
});
