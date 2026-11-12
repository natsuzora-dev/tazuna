import { contract, emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), title: z.string() },
  key: "id",
  invariants: {
    titled: ({ record }) => {
      if (record.title === "") throw new Error("the task has no title");
      return true;
    },
  },
});

export const { command, createEvent } = service({ description: "Keep the tasks", entities: { Task } });

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title })]);

export const todo = contract({ addTask });
