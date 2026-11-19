import { scenario } from "./screens.ts";

export const start = scenario("Start the service; pickScreen closes with a number below the count; no violation", {
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [] },
  when: (_w) => {},
  then: () => [],
});
