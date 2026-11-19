import { counterScreen, scenario } from "./screens.ts";

export const setCount = scenario({
  description: "Set the count; no violation",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [] },
  when: (w) => {
    w.user.operate(w.startup.screen(counterScreen), "countSet", { count: 3 });
  },
  then: () => [],
});
