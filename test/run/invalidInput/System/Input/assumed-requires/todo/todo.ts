import { entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const { query } = service({ description: "Keep the tasks", entities: { Task } });

export const taskTitle = query({
  input: { taskId: z.string() },
  output: { title: Task.fields.title.nullable() },
  requires: { named: ({ input }) => input.taskId !== "" },
}).resolve(({ input, records }) => ({ title: records.Task.get(input.taskId)?.title ?? null }));
