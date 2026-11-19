import { arm, scenario } from "./threads.ts";

export const tiedThreads = scenario({
  description:
    "Arm at 11:00; the deadlines of first and second tie, and each posts a note and a reply to it and counts them, so the two orders are searched. The reply's replyTo is ref.self(), so renaming the created keys there too makes the two orders' records equal; no violation",
  given: { start: "2026-10-25T11:00:00+09:00", records: { Note: [], Count: { notes: 0 } }, peers: [] },
  when: (w) => {
    w.client.send(arm, {});
  },
  then: () => [],
});
