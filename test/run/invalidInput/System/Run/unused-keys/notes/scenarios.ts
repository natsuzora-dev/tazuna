import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addNote, addTask } from "./notes.ts";

export const addNamedNote = scenario(
  "Add a task, naming N-milk the note that noteOnTask creates for it, then add the note N-milk; createKey gave N-milk, so addNote is rejected with already-exists and test reports nothing",
  [
    at("2026-10-25T09:00:00+09:00"),
    send(addTask, { taskId: "task-1" }, { keys: { Note: ["N-milk"] } }),
    send(addNote, { noteId: "N-milk", label: "again" }),
  ],
);

export const nameTwoNotes = scenario(
  "Add a task, naming two notes although noteOnTask creates one; createKey does not return N-eggs, so test reports unusedKeys",
  [at("2026-10-25T09:00:00+09:00"), send(addTask, { taskId: "task-1" }, { keys: { Note: ["N-milk", "N-eggs"] } })],
);
