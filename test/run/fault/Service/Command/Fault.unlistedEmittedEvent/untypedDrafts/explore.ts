import { domain, explore } from "@natsuzora-dev/tazuna";
import { dropDraft, saveDraft } from "./drafts.ts";

export const untypedDraftsExplore = explore({
  service: "untypedDrafts",
  depth: 2,
  domains: [domain(saveDraft.input.draftId, ["draft-1"]), domain(dropDraft.input.draftId, ["note-1"])],
});
