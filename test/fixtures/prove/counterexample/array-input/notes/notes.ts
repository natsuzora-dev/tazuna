import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Note = entity({
  description: "A note",
  fields: { id: z.string(), tagCount: z.int().min(0), pinned: z.boolean() },
  key: "id",
  invariants: {
    fewTags: ({ record }) => record.tagCount <= 1,
  },
});

export const { command, createEvent, bounds } = service({
  name: "notes",
  description: "Keep the notes",
  entities: { Note },
});

export const noteAdded = createEvent({ entity: Note });

export const addNote = command({
  callers: ["client"],
  input: { noteId: Note.fields.id, tags: z.array(z.string().min(1)).max(3) },
  requires: { distinct: ({ input }) => input.tags.every((t) => input.tags.filter((u) => u === t).length === 1) },
  emits: [noteAdded],
}).decide(({ input }) => [
  emit(noteAdded, {
    id: input.noteId,
    tagCount: input.tags.length,
    pinned: input.tags.some((t) => t === "pin") || input.tags.length > 0,
  }),
]);

export const notesBounds = bounds({ creates: { Note: 2 } });
