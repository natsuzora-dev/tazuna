import { external, fulfilled } from "@natsuzora-dev/tazuna";
import { catalog } from "../catalog/contract.ts";
import { scenario, shelfScreen } from "./shelf.ts";

export const answerUnsorted = scenario({
  description: "Answer the items out of n order; test reports answerOutputSchema",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [external(catalog)] },
  when: (w) => {
    w.net.deliver(w.startup.request(catalog.numbers));
    w.net.deliver(
      w.peer.catalog.answer(
        w.startup.request(catalog.numbers),
        fulfilled({
          items: [
            { n: 2, name: "b" },
            { n: 1, name: "a" },
          ],
        }),
      ),
    );
  },
  then: () => [],
});

export const pickTwice = scenario({
  description: "Pick the name a twice; test reports controlPayloadSchema",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [external(catalog)] },
  when: (w) => {
    w.user.operate(w.startup.screen(shelfScreen), "pick", { names: ["a", "a"] });
  },
  then: () => [],
});

export const answerItemWithUnknownField = scenario({
  description:
    "Answer an item with a field that Item does not have; an unknown field fails at any depth, so test reports answerOutputSchema",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [external(catalog)] },
  when: (w) => {
    w.net.deliver(w.startup.request(catalog.numbers));
    w.net.deliver(
      w.peer.catalog.answer(w.startup.request(catalog.numbers), fulfilled({ items: [{ n: 1, name: "a", note: "x" }] })),
    );
  },
  then: () => [],
});
