import { entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const { query } = service({ description: "Keep the tasks", entities: { Task } });

export const taskTitles = query({
  output: { titles: z.array(Task.fields.title) },
  ensures: {
    sorted: ({ output }) => output.titles.every((t, i, all) => i === 0 || (all[i - 1] ?? "") <= t),
    readsRecords: ({ output, records }) => output.titles.length === records.Task.length,
  },
}).resolve(({ records }) => ({ titles: records.Task.map((t) => t.title).sort() }));
