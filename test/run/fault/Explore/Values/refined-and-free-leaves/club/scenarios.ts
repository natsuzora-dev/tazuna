import { note, scenario } from "./club.ts";

export const noteTwo = scenario({
  description:
    "Note an email address and a name; explore sends invite with the address and, as its second value, the name, which only the email leaf's own refinement leaves free, so test reports exception of invite",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [] },
  when: (w) => {
    for (const text of ["ann@example.com", "Alice"]) w.client.send(note, { text });
  },
  then: () => [],
});
