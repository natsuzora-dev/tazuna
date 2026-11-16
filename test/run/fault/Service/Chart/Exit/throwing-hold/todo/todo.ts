import { entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const { machine, scenario } = service({ description: "Watch the first task", entities: { Task } });

export const watcher = machine({
  description: "Copy the title of the first task",
  context: { title: z.string().default("") },
  initial: "watching",
  states: { watching: { held: { task: z.object(Task.fields) } } },
}).chart({
  states: {
    watching: {
      holds: {
        task: ({ records }) => {
          const task = records.Task.only();
          if (task === undefined) throw new Error("there is no task to watch");
          return task;
        },
      },
      entry: { assign: { title: ({ held }) => held.task.title } },
    },
  },
});
