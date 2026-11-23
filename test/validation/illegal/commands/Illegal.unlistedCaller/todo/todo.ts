import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const { command, automation, event, createEvent, contract } = service({
  name: "todo",
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAddedRecorded = createEvent({ entity: Task });
export const taskAdded = event({ payload: { taskId: Task.fields.id } });
export const noted = event({});

export const addTask = command({
  callers: ["client"],
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAddedRecorded, taskAdded],
}).decide(({ input }) => [
  emit(taskAddedRecorded, { id: input.taskId, title: input.title }),
  emit(taskAdded, { taskId: input.taskId }),
]);

// Only clients may send note, so the automation of todo itself may not.
export const note = command({ callers: ["client"], emits: [noted] }).decide(() => [emit(noted, {})]);

export const noteAdded = automation({ receives: { taskAdded }, commands: { note } }).send({});

export const todo = contract({ addTask, note });
