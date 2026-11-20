import { note, scenario } from "./club.ts";

export const noteTwo = scenario({
  description:
    "Note an email address and a code; no word fits both refined leaves of invite, and explore gives each leaf the word that fits it, so test reports exception of invite",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [] },
  when: (w) => {
    for (const text of ["ann@example.com", "ABC"]) w.client.send(note, { text });
  },
  then: () => [],
});
