import { parseInstant } from "@natsuzora-dev/tazuna";
import { given, listScreen, scenario } from "./screens.ts";

const arranged = given({ start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [] });

export const pickUnderDialog = scenario({
  description: "Pick a task while the dialog covers the list; test reports coveredByModal",
  given: arranged,
  when: (w) => {
    const list = w.startup.screen(listScreen);
    w.user.operate(list, "clear");
    w.user.operate(list, "pick", { taskId: "task-1" });
  },
  then: () => [],
});
