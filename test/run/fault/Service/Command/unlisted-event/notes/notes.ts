import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, event } = service({ description: "Keep the notes" });

export const noteAdded = event({ payload: { noteId: z.string() } });
const noteDrafted = event({ payload: { noteId: z.string() } });

export const addNote = command({
  input: { noteId: z.string() },
  emits: [noteAdded],
}).decide(({ input }) => [emit(noteDrafted, { noteId: input.noteId })]);
