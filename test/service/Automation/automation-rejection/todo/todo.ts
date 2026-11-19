import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { device } from "../device/contract.ts";

export const Task = entity({
  description: "A task of the user",
  fields: { id: z.string(), title: z.string() },
  key: "id",
});

export const { automation, command, createEvent, contract, given, scenario } = service({
  name: "todo",
  description: "Keep tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title })]);

export const notifyAdded = automation({
  receives: { taskAdded },
  commands: { showNotification: device.showNotification },
}).send({ input: ({ payload }) => ({ text: payload.title }), onRejected: [] });
