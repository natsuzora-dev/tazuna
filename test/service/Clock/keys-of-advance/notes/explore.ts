import { domain, explore } from "@natsuzora-dev/tazuna";
import { addNote, addTask, Note, noteByLabel } from "./notes.ts";

export const notesExplore = explore({
  service: "notes",
  depth: 2,
  domains: [
    domain(addTask.input.taskId, ["task-1"]),
    domain(Note.fields.id, ["N-first"]),
    domain(addNote.input.label, ["first"]),
    domain(noteByLabel.input.label, ["hourly"]),
  ],
});
