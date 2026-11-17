import { skip } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { linkScreen, scenario } from "./screens.ts";

export const draftTwo = scenario(
  "Draft two notes linked both ways; each element of the bag of links holds both new keys, so pairing an element binds two keys at once and the binding cannot keep the choice open. The implementation links its second key to a third, and which of its links is the first decides which link differs, so verify reports Uncomparable.ambiguous",
  {
    given: {
      start: "2026-10-25T00:00:00Z",
      records: { Draft: [] },
      peers: { todo: skip(todo, "verify compares the subscriptions that the screen opens, not their answers") },
    },
    when: (w) => {
      const links = w.begin.screen(linkScreen);
      w.user.operate(links, "draft");
    },
    then: () => [],
  },
);
