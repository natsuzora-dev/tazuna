import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), title: z.string(), isDone: z.boolean() },
  key: "id",
});

export const { automation, command, query, machine, createEvent, updateEvent, contract, scenario } = service({
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
  input: { taskId: ref(Task) },
  emits: [taskCompleted],
}).decide(({ input }) => [emit(taskCompleted, { id: input.taskId, isDone: true })]);

export const completeDuplicates = automation({
  receives: { taskAdded },
  commands: { completeTask },
}).send({
  binds: {
    earlier: ({ payload, records }) =>
      records.Task.filter((t) => t.title === payload.title && t.id !== payload.id).only(),
  },
  input: ({ bound }) => ({ taskId: bound.earlier.id }),
});

export const backlog = contract({ addTask, completeTask });
