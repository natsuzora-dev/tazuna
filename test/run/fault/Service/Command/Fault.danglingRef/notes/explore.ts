import { domain, explore } from "@natsuzora-dev/tazuna";
import { Note } from "./notes.ts";

export const notesExplore = explore({ service: "notes", depth: 2, domains: [domain(Note.fields.id, ["note-1"])] });
