import { entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const { machine, scenario } = service({ name: "todo", description: "Watch the first task", entities: { Task } });

export const watcher = machine({
  description: "Copy the title of the first task",
  context: { title: z.string().default("") },
  initial: "running",
  states: { running: { initial: "watching", states: { watching: { held: { task: z.object(Task.fields) } } } } },
}).chart({
  states: {
    running: {
      initial: {
        with: {
          task: ({ records }) => {
            const task = records.Task.only();
            if (task === undefined) throw new Error("there is no task to watch");
            return task;
          },
        },
      },
    },
    watching: { entry: { assign: { title: ({ held }) => held.task.title } } },
  },
});
