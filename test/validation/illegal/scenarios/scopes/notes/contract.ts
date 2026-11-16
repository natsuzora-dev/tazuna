import { at, send } from "@natsuzora-dev/tazuna";
import { addNote, addTask, contract, noteList } from "./notes.ts";

export const notes = contract({
  addTask,
  addNote,
  noteList,
  states: { countedNote: [at("2026-10-25T08:00:00+09:00"), send(addNote, { noteId: "Note-1", label: "milk" })] },
});
