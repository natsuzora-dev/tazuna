import { domain, explore } from "@natsuzora-dev/tazuna";
import { addNote } from "./notes.ts";

export const notesExplore = explore({
  service: "notes",
  depth: 2,
  domains: [domain(addNote.input.noteId, ["note-1"])],
});
