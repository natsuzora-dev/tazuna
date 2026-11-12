import { contract, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const { query } = service({ description: "Keep the tasks", entities: { Task } });

export const taskTitle = query({
  input: { taskId: Task.fields.id },
  output: { title: Task.fields.title },
}).resolve(({ input, records }) => {
  const task = records.Task.get(input.taskId);
  if (task === undefined) throw "no task";
  return { title: task.title };
});

export const todo = contract({ taskTitle });
