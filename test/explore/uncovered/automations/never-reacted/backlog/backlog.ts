import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), title: z.string(), isDone: z.boolean() },
  key: "id",
});

export const { automation, command, createEvent, event, contract, scenario } = service({
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const choreAdded = event({ payload: { taskId: Task.fields.id } });

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded, choreAdded],
}).decide(({ input }) => [
  emit(taskAdded, { id: input.taskId, title: input.title, isDone: false }),
  ...(input.title.startsWith("Chore") ? [emit(choreAdded, { taskId: input.taskId })] : []),
]);

export const reminded = event({ payload: { taskId: Task.fields.id } });

export const remind = command({
  input: { taskId: Task.fields.id },
  emits: [reminded],
}).decide(({ input }) => [emit(reminded, { taskId: input.taskId })]);

export const remindChores = automation({
  receives: { choreAdded },
  commands: { remind },
}).send({
  input: ({ payload }) => ({ taskId: payload.taskId }),
});

export const remindOpenChores = automation({
  receives: { choreAdded },
  commands: { remind },
}).send({
  binds: { chore: ({ payload, records }) => records.Task.get(payload.taskId) },
  guard: { open: ({ bound }) => !bound.chore.isDone },
  input: ({ bound }) => ({ taskId: bound.chore.id }),
});

export const backlog = contract({ addTask, remind });
