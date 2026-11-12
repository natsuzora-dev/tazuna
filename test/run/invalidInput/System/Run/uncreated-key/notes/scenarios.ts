import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addNote, addTask } from "./notes.ts";

export const addBeforeCreated = scenario(
  "Add the note Note-1 before noteOnTask creates it; Note-1 has the form of a createKey value of Note that createKey has not given, so test reports uncreatedKey",
  [
    at("2026-10-25T09:00:00+09:00"),
    send(addNote, { noteId: "Note-1", label: "direct" }),
    send(addTask, { taskId: "Task-1" }),
  ],
);

export const addAfterCreated = scenario(
  "Add the task Task-1, then the note Note-1 that noteOnTask created for it; Task-1 has the form of no own entity's key and createKey gave Note-1, so addNote is rejected with already-exists and test reports nothing",
  [
    at("2026-10-25T09:00:00+09:00"),
    send(addTask, { taskId: "Task-1" }),
    send(addNote, { noteId: "Note-1", label: "again" }),
  ],
);
