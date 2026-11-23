import { parseInstant } from "@natsuzora-dev/tazuna";
import { scenario, start, thread } from "./notes.ts";

export const replyToCreated = scenario({
  description:
    "Start and list the notes; the service posts a note and a reply to it. The implementation's keys are n1 and n2, and the reply's replyTo, a key position as ref.self(), holds n1, which stands for Note-1; no violation",
  given: { start: parseInstant("2026-10-25T00:00:00Z"), records: { Note: [] }, peers: [] },
  when: (w) => {
    w.client.as("client").send(start, {});
    w.client.as("client").call(thread, {});
  },
  then: () => [],
});

export const replyToOther = scenario({
  description:
    "Same inputs as replyToCreated; the implementation trace of this scenario lists a reply whose replyTo is n9, which does not stand for Note-1, so verify reports a mismatch",
  given: { start: parseInstant("2026-10-25T00:00:00Z"), records: { Note: [] }, peers: [] },
  when: (w) => {
    w.client.as("client").send(start, {});
    w.client.as("client").call(thread, {});
  },
  then: () => [],
});
