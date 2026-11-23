import { entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Note = entity({ description: "A note", fields: { id: z.string() }, key: "id" });

export const { command, machine, contract } = service({
  name: "notes",
  description: "Register a new note with tags, then ask for its labels",
  entities: { Note },
});

export const attach = command({
  callers: ["client", "tags"],
  input: { labelId: z.string(), noteId: z.string() },
  emits: [],
}).decide(() => []);
