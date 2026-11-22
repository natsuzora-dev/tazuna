import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario } from "./flags.ts";

export const addOne = scenario({
  description:
    "Add a task; flagger sends raise and lower from one state, and the one taken last decides the flag, so test reports stepOrder",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Flag: { isOn: false } }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1" });
  },
  then: () => [],
});
