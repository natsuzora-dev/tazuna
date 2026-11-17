import { entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Note = entity({ description: "A note", fields: { id: z.string() }, key: "id" });

export const { event } = service({ name: "todo", description: "Keep the tasks" });
export const { command, query } = service({ name: "todo", description: "Keep the notes", entities: { Note } });

export const taskAdded = event({});
export const writeNote = command({ emits: [] }).decide(() => []);
