import { bag, emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const Note = entity({
  description: "A note on a task",
  fields: { id: z.string(), taskId: ref(Task) },
  key: "id",
});

export const { automation, command, createEvent, event, machine, contract } = service({
  description: "Keep tasks, their notes and their ranks",
  entities: { Task, Note },
});

export const taskAdded = createEvent({ entity: Task });
export const noteAdded = createEvent({ entity: Note });
export const taskRanked = event({ payload: { taskId: z.string(), rank: z.int() } });

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title })]);

export const addNotes = command({
  input: { notes: bag(z.object({ noteId: Note.fields.id, taskId: ref(Task) })) },
  emits: [noteAdded],
}).decide(({ input }) => [input.notes.map((n) => emit(noteAdded, { id: n.noteId, taskId: n.taskId }))]);

export const noteEveryTask = automation({ receives: { taskAdded }, commands: { addNotes } }).send({
  input: ({ createKey, records }) => ({
    notes: records.Task.map((t) => ({ noteId: createKey(ref(Note)), taskId: t.id })),
  }),
});

export const rankTasks = command({ emits: [taskRanked] }).decide(({ records }) => {
  let rank = 0;
  return [records.Task.map((t) => emit(taskRanked, { taskId: t.id, rank: rank++ }))];
});

export const checkFirst = command({
  emits: [],
  requires: {
    firstIsMilk: ({ records }) => {
      let first: string | undefined;
      records.Task.map((t) => (first ??= t.title));
      return first === "Buy milk";
    },
  },
}).decide(() => []);

export const tracker = machine({
  description: "Remember the title that a Bag callback sees first",
  context: { firstTitle: z.string().default("") },
  receives: { taskAdded },
  initial: "tracking",
  states: { tracking: {} },
}).chart({
  on: {
    taskAdded: [
      {
        assign: {
          firstTitle: ({ records }) => {
            let first = "";
            records.Task.map((t) => (first ||= t.title));
            return first;
          },
        },
      },
    ],
  },
});

export const tasks = contract({ addTask, addNotes, rankTasks, checkFirst });
