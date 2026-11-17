import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task of the user", fields: { id: z.string() }, key: "id" });

export const { command, machine, event, createEvent, contract, scenario } = service({
  name: "todo",
  description: "Keep tasks and report when the deadline of each task comes",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });
export const reminded = event({ payload: { taskId: z.string() } });

export const addTask = command({ input: { taskId: Task.fields.id }, emits: [taskAdded] }).decide(({ input }) => [
  emit(taskAdded, { id: input.taskId }),
]);

export const remind = command({ input: { taskId: ref(Task) }, emits: [reminded] }).decide(({ input }) => [
  emit(reminded, { taskId: input.taskId }),
]);
