import { filteredScreen, listScreen, scenario } from "./picker.ts";

export const pickListed = scenario({
  description: "Pick a task from the list; test reports offersSchema",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [] },
  when: (w) => {
    w.user.operate(w.startup.screen(listScreen), "pick", { taskId: "task-1" });
  },
  then: () => [],
});

export const pickFiltered = scenario({
  description: "Pick a task from the filtered list; test reports offersSchema",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [] },
  when: (w) => {
    w.user.operate(w.startup.screen(filteredScreen), "pick", { taskId: "task-1" });
  },
  then: () => [],
});
