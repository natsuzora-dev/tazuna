import { domain, explore } from "@natsuzora-dev/tazuna";
import { catalog } from "../catalog/contract.ts";
import { shelfScreen } from "./shelf.ts";

export const shelfExplore = explore({
  service: "shelf",
  depth: 2,
  domains: [
    domain(catalog.numbers.output.items, [
      [
        { n: 2, name: "b" },
        { n: 1, name: "a" },
      ],
    ]),
    domain(shelfScreen.controls.pick.payload.names, []),
  ],
});
