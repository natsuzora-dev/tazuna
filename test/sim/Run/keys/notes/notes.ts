import { entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Note = entity({ description: "A note", fields: { id: z.string() }, key: "id" });

export const { command, machine, contract } = service({
  description: "Register a new note with tags, then ask for its labels",
  entities: { Note },
});

export const attach = command({ input: { labelId: z.string(), noteId: z.string() }, emits: [] }).decide(() => []);
