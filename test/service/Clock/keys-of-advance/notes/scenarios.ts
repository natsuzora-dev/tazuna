import { addNote, addTask, noteByLabel, scenario } from "./notes.ts";

export const namesOfAdvanceAndInput = scenario(
  "At 10:00 the hour deadline of hourly fires before addTask arrives and creates the note notes/Note-1; noteOnTask then creates the note notes/Note-2, so adding the two notes again, with the keys that noteByLabel answers, is rejected with already-exists",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: { Note: [] }, peers: [] },
    when: (w) => {
      w.client.send(addNote, { noteId: "N-first", label: "first" });
      w.clock.at("2026-10-25T10:00:00+09:00");
      w.client.send(addTask, { taskId: "task-1" });
      const hourlyNote = w.client.call(noteByLabel, { label: "hourly" });
      const taskNote = w.client.call(noteByLabel, { label: "task-1" });
      w.client.send(addNote, { noteId: hourlyNote.output.noteId, label: "again" });
      w.client.send(addNote, { noteId: taskNote.output.noteId, label: "again" });
    },
    then: () => [],
  },
);
