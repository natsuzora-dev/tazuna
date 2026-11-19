import { homeScreen, scenario } from "./loop.ts";

export const start = scenario({
  description:
    "Start the home screen; it opens the done screen again each time the done screen is done, without end, so the start message runs more than 10000 work items and test reports exceededMessageWork",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [] },
  when: (w) => {
    w.startup.screen(homeScreen);
  },
  then: () => [],
});
