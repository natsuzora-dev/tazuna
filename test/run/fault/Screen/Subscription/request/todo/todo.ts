import { entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const { query } = service({ description: "Keep the tasks", entities: { Task } });

export const recent = query({
  input: { limit: z.number().int().positive() },
  output: { titles: z.array(Task.fields.title) },
}).resolve(({ input, records }) => ({ titles: records.Task.slice(0, input.limit).map((t) => t.title) }));
