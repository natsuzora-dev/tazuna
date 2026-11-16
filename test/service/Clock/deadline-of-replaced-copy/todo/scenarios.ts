import { addTask, scenario } from "./todo.ts";

export const deadlineOfReplacedCopy = scenario(
  "Add task-1 at 10:00; the copy of task-1 enters waiting with an 11:00 deadline. At 11:00, before it processes that deadline, perTask reenters rows through an always transition, so the copy of task-1 ends, which cancels the 11:00 deadline, and a new copy of the same key enters waiting with a 12:00 deadline. The canceled 11:00 deadline does not reach the new copy, so the new copy reports at 12:00",
  {
    given: { start: "2026-10-25T10:00:00+09:00", records: { Task: [] }, peers: {} },
    when: (w) => {
      w.client.send(addTask, { taskId: "task-1" });
      w.clock.at("2026-10-25T13:00:00+09:00");
    },
    then: () => [],
  },
);
