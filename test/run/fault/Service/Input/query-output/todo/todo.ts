import { entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const { query, contract } = service({ description: "Count the tasks", entities: { Task } });

export const taskCount = query({
  output: {
    count: z.number().refine((count) => {
      if (count === 0) throw new Error("there is no task to count");
      return true;
    }),
  },
}).resolve(({ records }) => ({ count: records.Task.size }));

export const todo = contract({ taskCount });
