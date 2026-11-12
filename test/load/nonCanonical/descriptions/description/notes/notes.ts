import { contract, emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Note = entity({ description: "A note", fields: { id: z.string(), text: z.string() }, key: "id" });

export const { command, createEvent } = service({ description: "Keep notes", entities: { Note } });

export const noteAdded = createEvent({ entity: Note });

export const addNote = command({
  input: { noteId: Note.fields.id, text: Note.fields.text },
  emits: [noteAdded],
}).decide(({ input }) => [emit(noteAdded, { id: input.noteId, text: input.text })]);

export const notes = contract({ addNote });
