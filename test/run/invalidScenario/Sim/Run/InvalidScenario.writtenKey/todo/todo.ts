import { bag, emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string() }, key: "id" });
export const Note = entity({
  description: "A note on a task",
  fields: { id: z.string(), taskId: ref(Task) },
  key: "id",
});

export const { automation, command, query, createEvent, contract, scenario } = service({
  name: "todo",
  description: "Keep the tasks and a note on each",
  entities: { Task, Note },
});

export const taskAdded = createEvent({ entity: Task });
export const noteAdded = createEvent({ entity: Note });

export const addTask = command({ input: { taskId: Task.fields.id }, emits: [taskAdded] }).decide(({ input }) => [
  emit(taskAdded, { id: input.taskId }),
]);

export const addNote = command({
  input: { noteId: Note.fields.id, taskId: ref(Task) },
  emits: [noteAdded],
}).decide(({ input }) => [emit(noteAdded, { id: input.noteId, taskId: input.taskId })]);

export const noteAddedTask = automation({
  receives: { taskAdded },
  commands: { addNote },
}).send({ input: ({ payload, createKey }) => ({ noteId: createKey(ref(Note)), taskId: payload.id }) });

export const noteIds = query({ output: { noteIds: bag(Note.fields.id) } }).resolve(({ records }) => ({
  noteIds: records.Note.map((n) => n.id),
}));
