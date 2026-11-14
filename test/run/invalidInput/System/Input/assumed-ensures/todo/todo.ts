import { bag, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), title: z.string() },
  key: "id",
  unique: ["title"],
});

export const { query } = service({ description: "Keep the tasks", entities: { Task } });

export const taskTitles = query({
  output: { titles: bag(Task.fields.title) },
  ensures: {
    distinct: ({ output }) => output.titles.every((t) => output.titles.filter((u) => u === t).length === 1),
    readsRecords: ({ output, records }) => output.titles.length === records.Task.size,
  },
}).resolve(({ records }) => ({ titles: records.Task.map((t) => t.title) }));
