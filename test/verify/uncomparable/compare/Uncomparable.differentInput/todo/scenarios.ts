import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, removeTask, scenario } from "./todo.ts";

export const addAndRemove = scenario({
  description:
    "Add a task and remove it; the implementation trace of this scenario writes removeTask a second before addTask, so the spec, whose clock never goes back, takes it at another time, and verify reports differentInput",
  given: { start: parseInstant("2026-10-25T00:00:00Z"), records: {}, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1" });
    w.client.send(removeTask, { taskId: "task-1" });
  },
  then: () => [],
});
