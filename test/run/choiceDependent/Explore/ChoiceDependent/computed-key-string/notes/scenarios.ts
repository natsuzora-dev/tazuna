import { arm, scenario } from "./notes.ts";

export const tied = scenario({
  description:
    "Arm at 11:00; the deadlines of first and second tie, and each posts a note with a created key and counts it, so test runs both orders. Whichever clock posts first gets Note-1, so the announcements and the records differ only by a renaming of the keys in their ref() and key fields. Each announcement also carries the label notes/Note-9, which has the form of a created key but sits in a plain z.string() field, so it compares as text, and test reports nothing",
  given: { start: "2026-10-25T11:00:00+09:00", records: { Note: [], Count: { n: 0 } }, peers: [] },
  when: (w) => {
    w.client.send(arm, {});
  },
  then: () => [],
});
