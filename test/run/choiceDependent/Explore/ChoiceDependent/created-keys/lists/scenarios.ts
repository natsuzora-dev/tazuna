import { arm, scenario } from "./lists.ts";

export const tied = scenario({
  description:
    "Arm at 11:00; the deadlines of first and second tie, and each posts a note with a created key, a tag whose noteIds is an array of ref(Note), and a count, so test runs both orders. Whichever clock posts first gets Note-1, so the records differ only by a renaming of the keys in Note.id and the elements of Tag.noteIds, which are key positions in records as in lines, and test reports nothing",
  given: { start: "2026-10-25T11:00:00+09:00", records: { Note: [], Tag: [], Count: { n: 0 } }, peers: [] },
  when: (w) => {
    w.client.send(arm, {});
  },
  then: () => [],
});
