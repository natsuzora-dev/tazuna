import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, assignTask, scenario } from "./todo.ts";

export const assignedLate = scenario({
  description:
    "Add a task at 09:00 and let the clock reach 11:00 before assigning it; test reports missedResponse assigned, due at 10:00",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1" });
    w.clock.at(parseInstant("2026-10-25T11:00:00+09:00"));
    w.client.send(assignTask, { taskId: "task-1", assignee: "aki" });
  },
  then: () => [],
});

export const assignedInTime = scenario({
  description: "Add a task at 09:00 and assign it at 09:30; test reports nothing",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1" });
    w.clock.at(parseInstant("2026-10-25T09:30:00+09:00"));
    w.client.send(assignTask, { taskId: "task-1", assignee: "aki" });
    w.clock.at(parseInstant("2026-10-25T11:00:00+09:00"));
  },
  then: () => [],
});
