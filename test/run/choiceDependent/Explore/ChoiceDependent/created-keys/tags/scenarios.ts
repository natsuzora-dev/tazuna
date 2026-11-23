import { parseInstant } from "@natsuzora-dev/tazuna";
import { arm, scenario } from "./tags.ts";

export const tied = scenario({
  description:
    "Arm at 11:00; the deadlines of first and second tie, and each posts a note with a created key, a tag whose noteId reuses Note's key field schema, and a count, so test runs both orders. Whichever clock posts first gets Note-1, so the records differ only by a renaming of the keys in Note.id and Tag.noteId, which are key positions in records as in lines, and test reports nothing. The label tags/Note-9 sits in a plain z.string() field and compares as text",
  given: {
    start: parseInstant("2026-10-25T11:00:00+09:00"),
    records: { Note: [], Tag: [], Count: { n: 0 } },
    peers: [],
  },
  when: (w) => {
    w.client.as("client").send(arm, {});
  },
  then: () => [],
});
