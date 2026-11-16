import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./planner.ts";

export const deadlineMoved = scenario(
  "Add a task at 10:00 and another at 12:30; reminder computes its deadline again each time planner finishes processing addTask. The deadline becomes 13:00 after the first addTask and 14:00 after the second, so reminder notifies at 14:00",
  [
    at("2026-10-25T10:00:00+09:00"),
    send(addTask, { taskId: "task-1" }),
    at("2026-10-25T12:30:00+09:00"),
    send(addTask, { taskId: "task-2" }),
    at("2026-10-25T14:30:00+09:00"),
  ],
);

export const deadlinePassed = scenario(
  "Add the task now at 11:30; the deadline of reminder becomes 10:00, which has passed, so reminder notifies at 11:30, when planner finishes processing addTask",
  [at("2026-10-25T10:00:00+09:00"), at("2026-10-25T11:30:00+09:00"), send(addTask, { taskId: "now" })],
);
