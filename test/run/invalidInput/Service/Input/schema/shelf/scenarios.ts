import { external } from "@natsuzora-dev/tazuna";
import { catalog } from "../catalog/contract.ts";
import { scenario, shelfScreen } from "./shelf.ts";

export const answerUnsorted = scenario("Answer the items out of n order; test reports answerOutputSchema", {
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: { catalog: external(catalog) } },
  when: (w) => {
    w.net.deliver(w.startup.request(catalog.numbers));
    w.net.deliver(
      w.peer.catalog.answer(w.startup.request(catalog.numbers), {
        result: "fulfilled",
        output: {
          items: [
            { n: 2, name: "b" },
            { n: 1, name: "a" },
          ],
        },
      }),
    );
  },
  then: () => [],
});

export const pickTwice = scenario("Pick the name a twice; test reports controlPayloadSchema", {
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: { catalog: external(catalog) } },
  when: (w) => {
    w.user.operate(w.startup.screen(shelfScreen), "pick", { names: ["a", "a"] });
  },
  then: () => [],
});
