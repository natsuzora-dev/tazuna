import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, event, scenario } = service({ name: "untypedDrafts", description: "Keep the drafts" });

export const draftSaved = event({ payload: { draftId: z.string() } });
export const draftDropped = event({ payload: { draftId: z.string() } });

const numbered: string = JSON.parse("1");

export const saveDraft = command({
  input: { draftId: z.string() },
  emits: [draftSaved],
}).decide(() => [emit(draftDropped, { draftId: numbered })]);

export const dropDraft = command({
  input: { draftId: z.string() },
  emits: [draftDropped],
}).decide(({ input }) => [emit(draftDropped, { draftId: input.draftId })]);
