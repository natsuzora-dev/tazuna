import { entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task of the user", fields: { id: z.string() }, key: "id" });

export const Status = z.enum(["open", "done"]).meta({ id: "Status" });

export const { command, given, scenario } = service({ name: "todo", description: "Keep tasks", entities: { Task } });

export const mark = command({
  input: { taskId: Task.fields.id, status: Status },
  emits: [],
  ensures: { stillOpen: ({ input }) => input.status === "open" },
}).decide(() => []);
