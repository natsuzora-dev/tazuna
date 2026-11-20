import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const { automation, command, createEvent, contract, scenario } = service({
  name: "todo",
  description: "Keep the tasks and copy each added one under a created key",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title })]);

export const copyTask = command({ input: { taskId: Task.fields.id, title: Task.fields.title }, emits: [] }).decide(
  () => [],
);

export const copyAdded = automation({ receives: { taskAdded }, commands: { copyTask } }).send({
  input: ({ payload, createKey }) => ({ taskId: createKey<typeof Task>(JSON.parse('"Task"')), title: payload.title }),
});

export const todo = contract({ addTask });
