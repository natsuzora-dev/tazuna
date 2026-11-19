import { deleteNote, post, scenario } from "./notes.ts";

export const deleteRepliedNote = scenario({
  description:
    "Delete a note that another note replies to; the reply's replyTo, a ref.self(), still names the deleted note, so test reports danglingRef",
  given: { start: "2026-10-25T09:00:00+09:00", records: { Note: [] }, peers: [] },
  when: (w) => {
    w.client.send(post, { noteId: "note-1", replyTo: null });
    w.client.send(post, { noteId: "note-2", replyTo: "note-1" });
    w.client.send(deleteNote, { noteId: "note-1" });
  },
  then: () => [],
});
