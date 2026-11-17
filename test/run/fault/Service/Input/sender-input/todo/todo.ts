import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { notes } from "../notes/contract.ts";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const { automation, command, createEvent, contract, scenario } = service({
  name: "todo",
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title })]);

export const noteAdded = automation({
  receives: { taskAdded },
  commands: { addNote: notes.addNote },
}).send({ input: ({ payload }) => ({ text: payload.title }), onRejected: [] });
