import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, contract, event } = service({ name: "notes", description: "Keep notes" });

export const noteKept = event({ payload: { text: z.string() } });

export const addNote = command({
  input: { text: z.string().min(1) },
  emits: [noteKept],
}).decide(({ input }) => [emit(noteKept, { text: input.text })]);
