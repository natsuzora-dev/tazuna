import { entity, service, sortedBy } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), title: z.string(), addedAt: z.number() },
  key: "id",
});

export const { query } = service({ description: "Keep the tasks", entities: { Task } });

export const recent = query({
  input: { limit: z.number().int().positive() },
  output: { tasks: sortedBy(z.object({ title: Task.fields.title, addedAt: Task.fields.addedAt }), "addedAt") },
}).resolve(({ input, records }) => {
  const runs = records.Task.sortedBy((t) => t.addedAt);
  const ends = runs.map((_, i) => runs.slice(0, i + 1).reduce((n, run) => n + run.size, 0));
  // A page holds whole runs, since the tasks added at one time have no order.
  const page = runs.filter((_, i) => (ends[i] ?? 0) <= input.limit);
  return { tasks: page.map((run) => run.map((t) => ({ title: t.title, addedAt: t.addedAt }))) };
});
