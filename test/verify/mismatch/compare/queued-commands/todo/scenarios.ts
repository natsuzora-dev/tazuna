import { addTask, scenario } from "./todo.ts";

export const addTwice = scenario(
  "Add two tasks; the three commands that logAdded, countAdded, and scheduleAdded send do not cause one another, so verify treats as matching an implementation trace that sends the three events of the first addTask in reverse order; no violation",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: {} },
    when: (w) => {
      w.client.send(addTask, { taskId: "task-1" });
      w.client.send(addTask, { taskId: "task-2" });
    },
    then: () => [],
  },
);
