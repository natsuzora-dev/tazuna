import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario } from "./todo.ts";

export const addTwice = scenario({
  description:
    "Add two tasks; logAdded logs taskAdded, countLogged counts logged, and scheduleCounted schedules counted, so each event causes the next and logged, counted, and scheduled travel in that order on the one channel of todo's events. The trace sends the three events of the first addTask in reverse order, which breaks that order: lineOrder; for the second addTask it sends the answer last and taskAdded, on the channel of addTask's request, between logged and counted, which no channel orders",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [] },
  when: (w) => {
    w.client.as("client").send(addTask, { taskId: "task-1" });
    w.client.as("client").send(addTask, { taskId: "task-2" });
  },
  then: () => [],
});
