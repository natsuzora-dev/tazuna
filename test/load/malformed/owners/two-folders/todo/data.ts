import { entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string() }, key: "id" });

export const { event } = service({ name: "todo", description: "Keep the tasks", entities: { Task } });

export const taskAdded = event({});
