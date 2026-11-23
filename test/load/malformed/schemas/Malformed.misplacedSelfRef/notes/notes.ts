import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Note = entity({
  description: "A note, or a reply to the note replyTo names",
  fields: { id: z.string(), replyTo: ref.self().nullable() },
  key: "id",
});

export const { command, createEvent, contract } = service({
  name: "notes",
  description: "Keep notes and their replies",
  entities: { Note },
});

export const posted = createEvent({ entity: Note });

export const post = command({
  callers: ["client"],
  input: { noteId: Note.fields.id, replyTo: Note.fields.replyTo, quoted: z.object({ note: ref.self() }) },
  emits: [posted],
}).decide(({ input }) => [emit(posted, { id: input.noteId, replyTo: input.replyTo })]);

export const notes = contract({ post });
