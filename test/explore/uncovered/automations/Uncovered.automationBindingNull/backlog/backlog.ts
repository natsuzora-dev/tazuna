import { emit, entity, service } from "@natsuzora-dev/tazuna";
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
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title, isDone: false })]);

export const taskCompleted = updateEvent({ entity: Task, writes: ["isDone"] });

export const completeTask = command({
  input: { title: Task.fields.title },
  emits: [taskCompleted],
  binds: { task: ({ input, records }) => records.Task.filter((t) => t.title === input.title).only() },
  requires: { notDone: ({ bound }) => !bound.task.isDone },
}).decide(({ bound }) => [emit(taskCompleted, { id: bound.task.id, isDone: true })]);

export const completeAdded = automation({
  receives: { taskAdded },
  commands: { completeTask },
}).send({
  binds: { added: ({ payload, records }) => records.Task.get(payload.id) },
  input: ({ bound }) => ({ title: bound.added.title }),
});

export const backlog = contract({ addTask, completeTask });
