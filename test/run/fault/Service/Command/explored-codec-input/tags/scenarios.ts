import { scenario } from "./tags.ts";

export const nothingSent = scenario({
  description:
    "Send nothing; explore sends tag with a string from the input side of its codec, so test reports exception of tag",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [] },
  when: () => {},
  then: () => [],
});
