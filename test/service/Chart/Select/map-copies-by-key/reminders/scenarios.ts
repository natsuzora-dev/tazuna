import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { clearAll, starTask } from "./reminders.ts";

export const eventRoutedByKey = scenario(
  "Star task-1 and task-3; taskStarred reaches only the copy whose key taskId equals the taskId of the payload, so only the copy of task-1 notifies, and the taskStarred of task-3, which has no copy, reaches no copy",
  [at("2026-10-25T10:00:00+09:00"), send(starTask, { taskId: "task-1" }), send(starTask, { taskId: "task-3" })],
);

export const eventWithoutKeyFields = scenario(
  "Clear all; allCleared, whose payload has no taskId, reaches every copy",
  [at("2026-10-25T10:00:00+09:00"), send(clearAll, {})],
);
