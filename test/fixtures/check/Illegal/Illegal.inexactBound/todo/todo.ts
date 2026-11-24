import { entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string() }, key: "id" });

export const Note = entity({ description: "A note", fields: { id: z.string() }, key: "id" });

export const Tag = entity({ description: "A tag", fields: { id: z.string() }, key: "id" });

export const { bounds } = service({ name: "todo", description: "Keep the tasks", entities: { Task, Note, Tag } });

export const fewTasks = bounds({ creates: { Task: -1, Note: 1.5, Tag: 2 }, items: 0.5 });
