import { parseInstant } from "@natsuzora-dev/tazuna";
import { saveDraft, scenario } from "./drafts.ts";

export const saveOne = scenario({
  description:
    "Save a draft; saveDraft decides draftDropped, which its emits do not list, with a payload off its schema, so test reports unlistedEmittedEvent before any payload",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [] },
  when: (w) => {
    w.client.send(saveDraft, { draftId: "draft-1" });
  },
  then: () => [],
});
