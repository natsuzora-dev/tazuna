import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Note = entity({ description: "A note", fields: { id: z.string(), label: z.string() }, key: "id" });

export const { automation, command, event, createEvent } = service({
  description: "Add a note for each added task",
  entities: { Note },
});

export const taskAdded = event({ payload: { id: z.string() } });
export const noteAdded = createEvent({ entity: Note });

export const addTwoTasks = command({ input: { first: z.string(), second: z.string() }, emits: [taskAdded] }).decide(
  ({ input }) => [emit(taskAdded, { id: input.first }), emit(taskAdded, { id: input.second })],
);

export const addNote = command({ input: { noteId: Note.fields.id, label: z.string() }, emits: [noteAdded] }).decide(
  ({ input }) => [emit(noteAdded, { id: input.noteId, label: input.label })],
);

export const noteOnTask = automation({ receives: { taskAdded }, commands: { addNote } }).send({
  input: ({ createKey, payload }) => ({ noteId: createKey(ref(Note), "note"), label: payload.id }),
});
