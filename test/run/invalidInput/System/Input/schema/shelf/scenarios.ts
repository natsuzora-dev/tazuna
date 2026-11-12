import { at, mock, operate, scenario } from "@natsuzora-dev/tazuna";
import { catalog } from "../catalog/contract.ts";
import { shelfScreen, stocker } from "./shelf.ts";

export const answerUnsorted = scenario("Answer the items out of n order; test reports answerOutputSchema", [
  at("2026-10-25T09:00:00+09:00"),
  mock(stocker, [
    catalog.numbers,
    {
      result: "fulfilled",
      output: {
        items: [
          { n: 2, name: "b" },
          { n: 1, name: "a" },
        ],
      },
    },
  ]),
]);

export const pickTwice = scenario("Pick the name a twice; test reports controlPayloadSchema", [
  at("2026-10-25T09:00:00+09:00"),
  operate(shelfScreen, "pick", { names: ["a", "a"] }),
]);
