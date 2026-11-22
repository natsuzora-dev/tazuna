import { parseInstant } from "@natsuzora-dev/tazuna";
import { homeScreen, scenario } from "./loop.ts";

export const close = scenario({
  description: "Close the home screen over 10 nested screens",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [] },
  when: (w) => {
    w.user.operate(w.startup.screen(homeScreen), "close");
  },
  then: () => [],
});
