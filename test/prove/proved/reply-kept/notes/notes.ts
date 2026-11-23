import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Note = entity({
  description: "A note, or a reply to the note replyTo names",
  fields: { id: z.string(), replyTo: ref.self().nullable() },
  key: "id",
});

export const { command, createEvent, deleteEvent, bounds } = service({
  name: "notes",
  description: "Keep notes and their replies",
  entities: { Note },
});

export const posted = createEvent({ entity: Note });
export const deleted = deleteEvent({ entity: Note });

export const post = command({
  input: { noteId: Note.fields.id, replyTo: Note.fields.replyTo },
  emits: [posted],
}).decide(({ input }) => [emit(posted, { id: input.noteId, replyTo: input.replyTo })]);

export const deleteNote = command({
  input: { noteId: ref(Note) },
  emits: [deleted],
  requires: { noReplies: ({ input, records }) => !records.Note.some((n) => n.replyTo === input.noteId) },
}).decide(({ input }) => [emit(deleted, { id: input.noteId })]);

export const notesBounds = bounds({ creates: { Note: 2 } });
