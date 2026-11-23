import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string() }, key: "id" });

export const Note = entity({ description: "A note", fields: { id: z.string() }, key: "id" });

export const { command, createEvent, bounds } = service({
  name: "todo",
  description: "Keep the tasks and notes",
  entities: { Task, Note },
  invariants: { noNotes: ({ records }) => records.Note.size === 0 },
});

export const noteAdded = createEvent({ entity: Note });

export const addNote = command({ callers: ["client"], input: { noteId: Note.fields.id }, emits: [noteAdded] }).decide(
  ({ input }) => [emit(noteAdded, { id: input.noteId })],
);

// The bounds leave out Note, which the type of creates forbids and a value read at run time can do.
export const todoBounds = bounds({ creates: JSON.parse('{ "Task": 1 }') });
