import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Note = entity({
  description: "A note",
  fields: { id: z.string(), tagCount: z.int().min(0) },
  key: "id",
});

export const { command, createEvent, bounds } = service({
  name: "notes",
  description: "Keep the notes",
  entities: { Note },
});

export const noteAdded = createEvent({ entity: Note });

export const addNote = command({
  callers: ["client"],
  input: { noteId: Note.fields.id, tags: z.array(z.string().min(1)) },
  requires: {
    tagged: ({ input }) => input.tags.length > 0,
    pinnedFirst: ({ input }) => input.tags.length < 2 || input.tags.some((t) => t === "pin"),
  },
  emits: [noteAdded],
}).decide(({ input }) => [emit(noteAdded, { id: input.noteId, tagCount: input.tags.length })]);

export const notesBounds = bounds({ creates: { Note: 1 } });
