import { entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), points: z.int() }, key: "id" });

export const { machine, scenario } = service({
  name: "todo",
  description: "Watch the points of the tasks",
  entities: { Task },
});

export const watcher = machine({
  description: "Copy the total points of the tasks",
  context: { total: z.int().default(0) },
  initial: "running",
  states: { running: { initial: "watching", states: { watching: { held: { total: z.int() } } } } },
}).chart({
  states: {
    running: { initial: { with: { total: ({ records }) => records.Task.sum((task) => task.points) } } },
    watching: { entry: { assign: { total: ({ held }) => held.total } } },
  },
});
