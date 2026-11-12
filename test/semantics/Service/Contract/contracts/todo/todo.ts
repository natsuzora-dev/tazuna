import { emit, entity, ref, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task of the user",
  fields: { id: z.string(), title: z.string() },
  key: "id",
  invariants: { titleNotBlank: ({ record }) => record.title !== "" },
});

export const Board = singleEntity({
  description: "A task that the user highlighted, and how many times",
  fields: { pinned: ref(Task).nullable().default(null), pins: z.number().default(0) },
  invariants: { fewPins: ({ record }) => record.pins < 3 },
});

export const { command, query, createEvent, updateEvent } = service({
  description: "Keep tasks",
  entities: { Task, Board },
  invariants: { uniqueTitles: ({ records }) => new Set(records.Task.map((t) => t.title)).size === records.Task.length },
});

export const taskAdded = createEvent({ entity: Task });
export const taskRenamed = updateEvent({
  entity: Task,
  writes: ["title"],
});

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title })]);

export const renameTask = command({
  input: { taskId: ref(Task), title: Task.fields.title },
  emits: [taskRenamed],
  binds: { task: ({ input, records }) => records.Task.get(input.taskId) },
  requires: { changesTitle: ({ input, bound }) => bound.task.title !== input.title },
  ensures: {
    renamed: ({ input, records, bound }) =>
      bound.task.title !== input.title && records.Task.get(input.taskId)?.title === input.title,
  },
}).decide(({ input }) => [
  emit(taskRenamed, { id: input.taskId, title: "" }),
  emit(taskRenamed, { id: input.taskId, title: input.title }),
]);

export const taskPinned = updateEvent({
  entity: Board,
  writes: ["pinned", "pins"],
});

export const pinTask = command({
  input: { taskId: ref(Task) },
  emits: [taskPinned],
  requires: { pinsLeft: ({ records }) => records.Board.pins < 2 },
}).decide(({ input, records }) => [emit(taskPinned, { pinned: input.taskId, pins: records.Board.pins + 1 })]);

export const pinTaskByTitle = command({
  input: { title: Task.fields.title },
  emits: [taskPinned],
  binds: { task: ({ input, records }) => records.Task.find((t) => t.title === input.title) },
  requires: { pinsLeft: ({ records }) => records.Board.pins < 2 },
}).decide(({ records, bound }) => [emit(taskPinned, { pinned: bound.task.id, pins: records.Board.pins + 1 })]);

export const taskTitles = query({
  output: { titles: z.array(Task.fields.title) },
  ensures: { sorted: ({ output }) => output.titles.every((t, i) => i === 0 || (output.titles[i - 1] ?? "") <= t) },
}).resolve(({ records }) => ({ titles: records.Task.map((t) => t.title).sort() }));
