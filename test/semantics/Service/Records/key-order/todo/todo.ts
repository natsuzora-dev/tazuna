import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task of the user", fields: { id: z.string() }, key: "id" });

export const { command, event, createEvent } = service({ description: "Keep tasks", entities: { Task } });

export const taskAdded = createEvent({ entity: Task });

export const firstTaskPicked = event({ payload: { id: z.string() } });

export const addTask = command({ input: { taskId: z.string() }, emits: [taskAdded] }).decide(({ input }) => [
  emit(taskAdded, { id: input.taskId }),
]);

export const pickFirstTask = command({ emits: [firstTaskPicked] }).decide(({ records }) =>
  records.Task.slice(0, 1).map((task) => emit(firstTaskPicked, { id: task.id })),
);
