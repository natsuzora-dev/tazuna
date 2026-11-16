import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Note = entity({ description: "A note", fields: { id: z.string(), label: z.string() }, key: "id" });

export const { automation, command, event, createEvent, machine } = service({
  description: "Add a note for each task, and an hourly note an hour after the service begins",
  entities: { Note },
});

export const taskAdded = event({ payload: { id: z.string() } });
export const noteAdded = createEvent({ entity: Note });

export const addTask = command({ input: { taskId: z.string() }, emits: [taskAdded] }).decide(({ input }) => [
  emit(taskAdded, { id: input.taskId }),
]);

export const addNote = command({ input: { noteId: Note.fields.id, label: z.string() }, emits: [noteAdded] }).decide(
  ({ input }) => [emit(noteAdded, { id: input.noteId, label: input.label })],
);

export const noteOnTask = automation({ receives: { taskAdded }, commands: { addNote } }).send({
  input: ({ createKey, payload }) => ({ noteId: createKey(ref(Note)), label: payload.id }),
});

export const hourly = machine({
  description: "Add the hourly note an hour after the service begins",
  commands: { addNote },
  initial: "waiting",
  states: { waiting: {}, noting: {}, done: {} },
}).chart({
  states: {
    waiting: { after: { hour: { delay: { hours: 1 }, onFired: [{ target: "noting" }] } } },
    noting: {
      sends: {
        addNote: {
          input: ({ createKey }) => ({ noteId: createKey(ref(Note)), label: "hourly" }),
          onAccepted: [{ target: "done" }],
          onRejected: [{ target: "done" }],
        },
      },
    },
  },
});
