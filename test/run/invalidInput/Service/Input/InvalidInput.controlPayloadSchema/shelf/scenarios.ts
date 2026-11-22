import { external, parseInstant } from "@natsuzora-dev/tazuna";
import { catalog } from "../catalog/contract.ts";
import { scenario, shelfScreen } from "./shelf.ts";

export const pickTwice = scenario({
  description: "Pick the name a twice; test reports controlPayloadSchema",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [external(catalog)] },
  when: (w) => {
    w.user.operate(w.startup.screen(shelfScreen), "pick", { names: ["a", "a"] });
  },
  then: () => [],
});
