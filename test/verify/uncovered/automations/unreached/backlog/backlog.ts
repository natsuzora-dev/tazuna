import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), title: z.string(), isDone: z.boolean() },
  key: "id",
});

export const { automation, command, createEvent, updateEvent, contract, scenario } = service({
  name: "backlog",
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  callers: ["client"],
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title, isDone: false })]);

export const taskCompleted = updateEvent({ entity: Task, writes: ["isDone"] });

export const completeTask = command({
  callers: ["client", "backlog"],
  input: { taskId: Task.fields.id },
  emits: [taskCompleted],
  binds: { task: ({ input, records }) => records.Task.get(input.taskId) },
  requires: { notDone: ({ bound }) => !bound.task.isDone },
}).decide(({ bound }) => [emit(taskCompleted, { id: bound.task.id, isDone: true })]);

export const completeChores = automation({
  receives: { taskAdded },
  commands: { completeTask },
}).send({
  binds: { added: ({ payload, records }) => records.Task.get(payload.id) },
  guard: { chore: ({ bound }) => bound.added.title.startsWith("Chore") },
  input: ({ bound }) => ({ taskId: bound.added.id }),
});

export const completeDuplicates = automation({
  receives: { taskAdded },
  commands: { completeTask },
}).send({
  binds: {
    earlier: ({ payload, records }) =>
      records.Task.filter((t) => t.title === payload.title && t.id !== payload.id && !t.isDone).only(),
  },
  input: ({ bound }) => ({ taskId: bound.earlier.id }),
});

export const backlog = contract({ addTask, completeTask });
