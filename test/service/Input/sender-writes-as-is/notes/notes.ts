import { service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, contract } = service({ name: "notes", description: "Keep notes" });

export const addNote = command({ input: { text: z.string().trim() }, emits: [] }).decide(() => []);
