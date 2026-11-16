import { bag, emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { notes } from "../notes/contract.ts";

export const Label = entity({
  description: "A label of a note",
  fields: { id: z.string(), noteId: z.string() },
  key: "id",
});

export const { automation, command, createEvent, event, query, contract } = service({
  description: "Label each registered note, and tell notes the label",
  entities: { Label },
});

export const registered = event({ payload: { noteId: z.string() } });
export const labelAddedRecorded = createEvent({ entity: Label });

export const register = command({ input: { noteId: z.string() }, emits: [registered] }).decide(({ input }) => [
  emit(registered, { noteId: input.noteId }),
]);

export const addLabel = command({
  input: { labelId: Label.fields.id, noteId: Label.fields.noteId },
  emits: [labelAddedRecorded],
}).decide(({ input }) => [emit(labelAddedRecorded, { id: input.labelId, noteId: input.noteId })]);

export const labelRegistered = automation({ receives: { registered }, commands: { addLabel } }).send({
  input: ({ payload, createKey }) => ({ labelId: createKey(ref(Label)), noteId: payload.noteId }),
});

export const announceRegistered = automation({ receives: { registered }, commands: { attach: notes.attach } }).send({
  input: ({ payload, createKey }) => ({ labelId: createKey(ref(Label)), noteId: payload.noteId }),
  onRejected: [],
});

export const labels = query({
  output: { labels: bag(z.object({ labelId: ref(Label), noteId: Label.fields.noteId })) },
}).resolve(({ records }) => ({ labels: records.Label.map((l) => ({ labelId: l.id, noteId: l.noteId })) }));
