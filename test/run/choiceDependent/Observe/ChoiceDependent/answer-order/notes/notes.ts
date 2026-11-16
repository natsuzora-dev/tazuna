import { externalService } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command } = externalService({ description: "Keep the notes" });

export const saveNote = command({
  input: { text: z.string() },
  emits: [],
  rejects: ["invalid-input", "requires", "unavailable", "reused-id"],
});
