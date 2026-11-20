import { scenario } from "./screens.ts";

export const start = scenario({
  description:
    "Start the service; the initialContext of counterScreen returns the text of an Instant, which the context schema does not encode, so test reports initialContextSchema in Lean too, which once parsed the text",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [] },
  when: (_w) => {},
  then: () => [],
});
