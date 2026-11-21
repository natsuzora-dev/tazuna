import { entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task of the user", fields: { id: z.string() }, key: "id" });

export const { command, given, scenario } = service({ name: "todo", description: "Keep tasks", entities: { Task } });

export const flag = command({
  input: { taskId: Task.fields.id, urgent: z.boolean(), note: z.string().optional() },
  emits: [],
  ensures: {
    urgentNoted: ({ input }) => !(input.taskId === "task-9" && input.urgent && input.note === undefined),
  },
}).decide(() => []);
