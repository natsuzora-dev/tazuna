import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask, completeTask } from "./todo.ts";

export const completedInTime = scenario(
  "Add a task at 10:00, complete it at 10:30, and add another at 12:00; reminder exits waiting at 10:30, which cancels the 11:00 deadline, and notifies at the 13:00 deadline of waiting, which it reentered at 12:00",
  [
    at("2026-10-25T10:00:00+09:00"),
    send(addTask, { taskId: "task-1" }),
    at("2026-10-25T10:30:00+09:00"),
    send(completeTask, { taskId: "task-1" }),
    at("2026-10-25T12:00:00+09:00"),
    send(addTask, { taskId: "task-2" }),
    at("2026-10-25T13:30:00+09:00"),
  ],
);

export const guardedDeadline = scenario(
  "Add three tasks at 10:00, one at 12:00, and one at 13:30; at the 11:00 deadline, both hasManyTasks and hasTasks hold for counter, but counter selects the transition of hasManyTasks, the first in written order, and reports many. At the 13:00 deadline, no guard holds, so counter takes no transition and stays in waiting. The task at 13:30 does not make counter reenter waiting or set its deadline again, so counter reports nothing. Of the deadlines of reminder and counter due at one time, reminder fires first both times, as the first in entry order",
  [
    at("2026-10-25T10:00:00+09:00"),
    send(addTask, { taskId: "task-1" }),
    send(addTask, { taskId: "task-2" }),
    send(addTask, { taskId: "task-3" }),
    at("2026-10-25T12:00:00+09:00"),
    send(addTask, { taskId: "task-4" }),
    at("2026-10-25T13:30:00+09:00"),
    send(addTask, { taskId: "task-5" }),
    at("2026-10-25T15:00:00+09:00"),
  ],
);
