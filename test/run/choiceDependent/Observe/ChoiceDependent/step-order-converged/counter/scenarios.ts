import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./counter.ts";

export const addOne = scenario(
  "Add a task: the always guard of watcher reads the marks that mark adds, and the record change that mark makes evaluates the guard again, so in either order watcher ends in many; no violation",
  [at("2026-10-25T09:00:00+09:00"), send(addTask, { taskId: "task-1" })],
);
