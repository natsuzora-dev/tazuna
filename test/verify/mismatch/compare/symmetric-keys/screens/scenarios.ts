import { skip } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { linkScreen, scenario } from "./screens.ts";

const given = {
  start: "2026-10-25T00:00:00Z",
  records: { Draft: [] },
  peers: { todo: skip(todo, "verify compares the subscriptions that the screen opens, not their answers") },
} as const;

export const draftTwo = scenario(
  "Draft two notes linked both ways; each element of the bag of links holds both new keys, so the links bind the two keys in either of two ways, and no later line tells them apart. Both bindings agree with the trace; no violation",
  {
    given,
    when: (w) => {
      const links = w.begin.screen(linkScreen);
      w.user.operate(links, "draft");
    },
    then: () => [],
  },
);

export const draftTwoPointed = scenario(
  "Draft two notes linked both ways, then point at the first alone; the links bind the two keys in either of two ways, and the later subscription that names only the first keeps one of them; no violation",
  {
    given,
    when: (w) => {
      const links = w.begin.screen(linkScreen);
      w.user.operate(links, "draft");
      w.user.operate(links, "point");
    },
    then: () => [],
  },
);

export const draftTwoBroken = scenario(
  "Draft two notes linked both ways; the implementation links its second key to a third, so no binding of the two keys agrees with the links and verify reports Mismatch.request",
  {
    given,
    when: (w) => {
      const links = w.begin.screen(linkScreen);
      w.user.operate(links, "draft");
    },
    then: () => [],
  },
);
