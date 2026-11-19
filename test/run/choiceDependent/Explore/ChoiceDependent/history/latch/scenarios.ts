import { go, scenario } from "./latch.ts";

export const both = scenario("next and stop unordered; both orders end in idle, and resume would return to a or b", {
  given: { start: "2026-10-25T09:00:00Z", records: { Latch: { used: false } }, peers: {} },
  when: (w) => {
    w.client.send(go, { ks: ["next", "stop"] });
  },
  then: () => [],
});
