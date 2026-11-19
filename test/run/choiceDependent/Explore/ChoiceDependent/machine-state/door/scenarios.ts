import { go, scenario, touch } from "./door.ts";

export const openAndClose = scenario(
  "go emits opened and closed unordered. Taking opened first leaves the door shut, and taking closed first leaves it open. No line tells the orders apart, and the door's state does, so test reports stepOrder with the instances",
  {
    given: { start: "2026-10-25T09:00:00Z", records: { Door: { used: false } }, peers: {} },
    when: (w) => {
      w.client.send(go, { ks: ["open", "close"] });
    },
    then: () => [],
  },
);

export const touchedTwice = scenario(
  "touch emits touched by a and by b unordered, and the one taken last stays in the door's context. No line tells the orders apart, and the context does, so test reports stepOrder with the instances",
  {
    given: { start: "2026-10-25T09:00:00Z", records: { Door: { used: false } }, peers: {} },
    when: (w) => {
      w.client.send(touch, { by: ["a", "b"] });
    },
    then: () => [],
  },
);
