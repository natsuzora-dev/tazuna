import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTasks, completeTask } from "./greeter.ts";

export const copiesInKeyOrder = scenario(
  "Add task-1 and task-2; items lists task-2 before task-1, but items is a set, so greeter runs the copies in key order and greets task-1 first",
  [at("2026-10-25T10:00:00+09:00"), send(addTasks, { taskIds: ["task-1", "task-2"] })],
);

export const deadlineEndsWithCopy = scenario(
  "Add task-1 at 10:00, complete it at 10:30, and add task-2 at 11:30; the copy of task-1 leaves items and exits waiting, so its 11:00 deadline is canceled. Only the copy of task-2 reports, at 12:30",
  [
    at("2026-10-25T10:00:00+09:00"),
    send(addTasks, { taskIds: ["task-1"] }),
    at("2026-10-25T10:30:00+09:00"),
    send(completeTask, { taskId: "task-1" }),
    at("2026-10-25T11:30:00+09:00"),
    send(addTasks, { taskIds: ["task-2"] }),
    at("2026-10-25T13:00:00+09:00"),
  ],
);
