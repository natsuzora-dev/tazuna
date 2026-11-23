import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario } from "./backlog.ts";

export const work = scenario({
  description: "Add one task; its title is not empty, so the guard isTitled is never false",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
  },
  then: () => [],
});
