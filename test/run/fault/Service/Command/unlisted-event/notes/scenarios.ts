import { addNote, scenario } from "./notes.ts";

export const addOne = scenario({
  description:
    "Add a note; addNote decides noteDrafted, which notes.ts does not export, so it is no definition of the spec and test reports unlistedEmittedEvent with event null",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [] },
  when: (w) => {
    w.client.send(addNote, { noteId: "note-1" });
  },
  then: () => [],
});
