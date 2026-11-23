import { parseInstant, skip } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { given, scenario } from "./data.ts";
import { linkScreen } from "./screens.ts";

const arranged = given({
  start: parseInstant("2026-10-25T00:00:00Z"),
  records: { Draft: [] },
  peers: [skip(todo, "verify compares the subscriptions that the screen opens, not their answers")],
});

export const draftTwo = scenario({
  description:
    "Draft two notes linked both ways; the implementation subscribes to the links as todo, not as the screens service that a screen acts for when no user signed in, so verify reports Mismatch.caller",
  given: arranged,
  when: (w) => {
    const links = w.startup.screen(linkScreen);
    w.user.operate(links, "draft");
  },
  then: () => [],
});
