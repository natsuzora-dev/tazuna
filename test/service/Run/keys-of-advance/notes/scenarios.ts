import { addNote, addTask, scenario } from "./notes.ts";

export const namesOfAdvanceAndInput = scenario(
  "At 10:00 the hour deadline of hourly fires before addTask arrives and creates the note notes/Note-1; noteOnTask then creates the note notes/Note-2",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: { Note: [] }, peers: {} },
    when: (w) => {
      w.client.send(addNote, { noteId: "N-first", label: "first" });
      w.clock.at("2026-10-25T10:00:00+09:00");
      w.client.send(addTask, { taskId: "task-1" });
    },
    then: () => [],
  },
);
