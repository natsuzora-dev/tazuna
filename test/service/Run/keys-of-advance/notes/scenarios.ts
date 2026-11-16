import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addNote, addTask } from "./notes.ts";

export const namesOfAdvanceAndInput = scenario(
  "At 10:00 the hour deadline of hourly fires before addTask arrives and creates the note that the at line names N-hourly; noteOnTask then creates the note that addTask names N-task, so adding N-hourly and N-task again is rejected with already-exists",
  [
    at("2026-10-25T09:00:00+09:00"),
    send(addNote, { noteId: "N-first", label: "first" }),
    at("2026-10-25T10:00:00+09:00", { keys: { Note: ["N-hourly"] } }),
    send(addTask, { taskId: "task-1" }, { keys: { Note: ["N-task"] } }),
    send(addNote, { noteId: "N-hourly", label: "again" }),
    send(addNote, { noteId: "N-task", label: "again" }),
  ],
);
