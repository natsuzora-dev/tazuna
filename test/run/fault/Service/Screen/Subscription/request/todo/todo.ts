import { entity, service, sortedBy } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), title: z.string(), addedAt: z.int() },
  key: "id",
});

export const { query, contract } = service({ name: "todo", description: "Keep the tasks", entities: { Task } });

export const recent = query({
  input: { limit: z.int().positive() },
  output: { tasks: sortedBy(z.object({ title: Task.fields.title, addedAt: Task.fields.addedAt }), "addedAt") },
}).resolve(({ records }) => ({ tasks: records.Task.map((t) => ({ title: t.title, addedAt: t.addedAt })) }));
