import { announce, detailScreen, scenario, thirdPanel } from "./panels.ts";

export const closeThird = scenario(
  "The left and right panels open their details in either order, then the third panel opens a third detail and the user closes it. The operation line names the third detail as the third open detail in either order, so test reports nothing",
  {
    given: { start: "2026-10-25T09:00:00Z", records: { Board: { used: false } }, peers: [] },
    when: (w) => {
      w.client.send(announce, {});
      const shown = w.user.operate(w.startup.screen(thirdPanel), "show");
      w.user.operate(shown.screen(detailScreen), "close");
    },
    then: () => [],
  },
);
