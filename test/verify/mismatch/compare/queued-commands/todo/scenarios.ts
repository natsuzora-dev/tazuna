import { addTask, scenario } from "./todo.ts";

export const addTwice = scenario(
  "Add two tasks; logAdded, countAdded, and scheduleAdded send their commands in that order through the internal queue, so logged, counted, and scheduled travel in that order on the one channel of todo's events. The trace sends the three events of the first addTask in reverse order, which breaks that order: lineOrder; for the second addTask it sends the answer last and taskAdded, on the channel of addTask's request, between logged and counted, which no channel orders",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: {} },
    when: (w) => {
      w.client.send(addTask, { taskId: "task-1" });
      w.client.send(addTask, { taskId: "task-2" });
    },
    then: () => [],
  },
);
