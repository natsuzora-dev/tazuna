import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask, pickTask } from "./todo.ts";

export const leftRegionWins = scenario(
  "Add the task left; reminder selects the transition of leftWaiting in the region left over the transition of running, and notifies left",
  [at("2026-10-25T10:00:00+09:00"), send(addTask, { taskId: "left" })],
);

export const rightRegionWins = scenario(
  "Add the task right; reminder also selects the transition of rightWaiting in the region right, written later, over the transition of running, and notifies right",
  [at("2026-10-25T10:00:00+09:00"), send(addTask, { taskId: "right" })],
);

export const ancestorWhenNoDescendant = scenario(
  "Add the task other; only when no descendant state selects a transition does reminder go to stopping through the transition of running and notify running",
  [at("2026-10-25T10:00:00+09:00"), send(addTask, { taskId: "other" })],
);

export const copyWins = scenario(
  "Pick task-1 and then task-2; picker selects the transition of the copy task-1 over the transition of the map state rows and notifies task-1. The copy task-2, which selected no transition, does not exit rows either, so picking task-2 next notifies task-2",
  [at("2026-10-25T10:00:00+09:00"), send(pickTask, { taskId: "task-1" }), send(pickTask, { taskId: "task-2" })],
);

export const mapWhenNoCopy = scenario(
  "Pick task-3; only when no copy has a guard that holds does picker go to rowsStopping through the transition of rows and notify rows",
  [at("2026-10-25T10:00:00+09:00"), send(pickTask, { taskId: "task-3" })],
);
