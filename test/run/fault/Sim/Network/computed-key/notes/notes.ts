import { entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Note = entity({ description: "A note", fields: { id: z.string() }, key: "id" });

export const { query, contract, scenario } = service({
  name: "notes",
  description: "Guess a note key by computing it",
  entities: { Note },
});

export const guess = query({ output: { noteId: z.string() } }).resolve(() => ({ noteId: "notes/Note-9" }));

export const notes = contract({ guess });
