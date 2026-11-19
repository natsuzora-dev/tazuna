import { doneScreen, scenario } from "./closer.ts";

export const closeDone = scenario("Close the done screen; test reports screenOutputSchema", {
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [] },
  when: (w) => {
    w.user.operate(w.startup.screen(doneScreen), "close");
  },
  then: () => [],
});
