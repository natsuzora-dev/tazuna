import { parseInstant } from "@natsuzora-dev/tazuna";
import { given, listScreen, scenario } from "./screens.ts";

const arranged = given({ start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [] });

export const pickUnoffered = scenario({
  description: "Pick a task that the list does not show; test reports unofferedPayload",
  given: arranged,
  when: (w) => {
    w.user.operate(w.startup.screen(listScreen), "pick", { taskId: "task-3" });
  },
  then: () => [],
});
