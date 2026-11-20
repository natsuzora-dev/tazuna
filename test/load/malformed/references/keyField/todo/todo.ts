import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

const Tag = entity({ description: "A tag", fields: { id: z.string() }, key: "id" });

export const Task = entity({ description: "A task", fields: { id: z.string(), tag: Tag.fields.id }, key: "id" });

export const { command, createEvent } = service({
  name: "todo",
  description: "Keep tasks whose tag field reuses the key field of an entity that is not exported",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({ input: { id: z.string(), tag: z.string() }, emits: [taskAdded] }).decide(
  ({ input }) => [emit(taskAdded, input)],
);
