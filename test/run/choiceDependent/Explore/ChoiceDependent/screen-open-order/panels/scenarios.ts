import { announce, scenario } from "./panels.ts";

export const announceOnce = scenario({
  description:
    "Both panels take ready, and their claim commands both write the board, so test runs them in either order; each panel then opens a detail screen. Either order opens the same two screens, each named by the panel that opened it, so test reports nothing",
  given: { start: "2026-10-25T09:00:00Z", records: { Board: { used: false } }, peers: [] },
  when: (w) => {
    w.client.send(announce, {});
  },
  then: () => [],
});
