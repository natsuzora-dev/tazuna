import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addNote, addTask } from "./notes.ts";

export const addCountedNote = scenario(
  "Add a task, then the note Note-1 that noteOnTask created for it; Note-1 counts the notes that createKey gave, so check reports countedKey",
  [
    at("2026-10-25T09:00:00+09:00"),
    send(addTask, { taskId: "task-1" }),
    send(addNote, { noteId: "Note-1", label: "again" }),
  ],
);
