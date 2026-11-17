import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "", fields: { id: z.string(), title: z.string() }, key: "id" });

export const { command, createEvent, machine, contract } = service({
  name: "todo",
  description: "",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title })]);

export const tracker = machine({ description: "", initial: "idle", states: { idle: {} } }).chart({});

export const todo = contract({ addTask });
