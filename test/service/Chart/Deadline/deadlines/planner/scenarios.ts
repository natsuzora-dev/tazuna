import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, given, scenario } from "./planner.ts";

const arranged = given({ start: parseInstant("2026-10-25T10:00:00+09:00"), records: {}, peers: [] });

export const deadlineMoved = scenario({
  description:
    "Add a task at 10:00 and another at 12:30; reminder enters waiting again on each taskAdded, which fixes its deadline anew. The deadline becomes 13:00 after the first addTask and 14:00 after the second, so reminder notifies at 14:00; fixedReminder does not enter waiting again, so it notifies at 12:00",
  given: arranged,
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1" });
    w.clock.at(parseInstant("2026-10-25T12:30:00+09:00"));
    w.client.send(addTask, { taskId: "task-2" });
    w.clock.at(parseInstant("2026-10-25T14:30:00+09:00"));
  },
  then: () => [],
});

export const deadlinePassed = scenario({
  description:
    "Add the task now at 11:30; reminder enters waiting again with its deadline at 10:00, which has passed, so reminder notifies at 11:30, when planner finishes processing addTask",
  given: arranged,
  when: (w) => {
    w.clock.at(parseInstant("2026-10-25T11:30:00+09:00"));
    w.client.send(addTask, { taskId: "now" });
  },
  then: () => [],
});
