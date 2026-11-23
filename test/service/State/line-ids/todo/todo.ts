import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task of the user", fields: { id: z.string() }, key: "id" });
export const Note = entity({
  description: "A note on a task",
  fields: { id: z.string(), taskId: ref(Task) },
  key: "id",
});

export const Tag = entity({
  description: "A card of a task",
  fields: { id: z.string(), taskId: ref(Task) },
  key: "id",
});

export const { automation, command, createEvent, machine, contract, given, scenario } = service({
  name: "todo",
  description: "Keep tasks",
  entities: { Task, Note, Tag },
});

export const taskAdded = createEvent({ entity: Task });
export const noteAdded = createEvent({ entity: Note });
export const tagAdded = createEvent({ entity: Tag });

export const addTask = command({ callers: ["client"], input: { taskId: Task.fields.id }, emits: [taskAdded] }).decide(
  ({ input }) => [emit(taskAdded, { id: input.taskId })],
);

export const addNote = command({
  callers: ["client", "todo"],
  input: { noteId: Note.fields.id, taskId: ref(Task) },
  emits: [noteAdded],
}).decide(({ input }) => [emit(noteAdded, { id: input.noteId, taskId: input.taskId })]);

export const noteAddedTask = automation({
  receives: { taskAdded },
  commands: { addNote },
}).send({ input: ({ payload, createKey }) => ({ noteId: createKey(ref(Note)), taskId: payload.id }) });

export const addTag = command({
  callers: ["client", "todo"],
  input: { tagId: Tag.fields.id, taskId: ref(Task) },
  emits: [tagAdded],
}).decide(({ input }) => [emit(tagAdded, { id: input.tagId, taskId: input.taskId })]);

export const tagger = machine({
  description:
    "When a task whose id starts with pin is added, reserve one card id and then attach a card with another id",
  context: { kept: z.string().nullable().default(null) },
  receives: { taskAdded },
  commands: { addTag },
  initial: "idle",
  states: { idle: {}, tagging: { held: { taskId: ref(Task) } } },
}).chart({
  states: {
    idle: {
      on: {
        taskAdded: [
          {
            guard: { pinned: ({ payload }) => payload.id.startsWith("pin") },
            target: "tagging",
            assign: { kept: ({ createKey }) => createKey(ref(Tag)) },
            with: { taskId: ({ payload }) => payload.id },
          },
        ],
      },
    },
    tagging: {
      sends: {
        addTag: {
          input: ({ held, createKey }) => ({ tagId: createKey(ref(Tag)), taskId: held.taskId }),
          onAccepted: [{ target: "idle" }],
          onRejected: [{ target: "idle" }],
        },
      },
    },
  },
});
