import { parseInstant } from "@natsuzora-dev/tazuna";
import { go, scenario } from "./latch.ts";

export const both = scenario({
  description: "next and stop unordered; both orders end in idle, and resume would return to a or b",
  given: { start: parseInstant("2026-10-25T09:00:00Z"), records: { Latch: { used: false } }, peers: [] },
  when: (w) => {
    w.client.as("client").send(go, { ks: ["next", "stop"] });
  },
  then: () => [],
});
