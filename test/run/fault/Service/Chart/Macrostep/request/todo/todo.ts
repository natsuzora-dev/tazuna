import { bag, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const { query, contract } = service({ name: "todo", description: "Keep the tasks", entities: { Task } });

export const titled = query({
  callers: ["client", "emptyPrefixScreens", "screens"],
  input: { prefix: z.string() },
  output: { titles: bag(Task.fields.title) },
  requires: { notEmpty: ({ input }) => input.prefix !== "" },
}).resolve(({ input, records }) => ({
  titles: records.Task.filter((t) => t.title.startsWith(input.prefix)).map((t) => t.title),
}));
