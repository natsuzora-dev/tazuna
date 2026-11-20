import { note, scenario } from "./club.ts";

export const noteFive = scenario({
  description:
    "Note five texts, the last an email address; explore sends invite with that word, the only one its email refinement takes, so test reports exception of invite",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [] },
  when: (w) => {
    for (const text of ["one", "two", "three", "four", "ann@example.com"]) w.client.send(note, { text });
  },
  then: () => [],
});
