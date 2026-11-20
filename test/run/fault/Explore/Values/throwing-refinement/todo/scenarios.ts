import { scenario } from "./todo.ts";

export const nothingSent = scenario({
  description:
    "Send nothing; the refinement of the input of rename throws on the representative title explore tries, so test reports exception of rename",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [] },
  when: () => {},
  then: () => [],
});
