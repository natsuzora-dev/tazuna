import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./stats.ts";

export const addOne = scenario(
  "Add a task: countAdded and rememberTitle both write the whole Stats record from the record they read, so in either order Stats counts the task and remembers its title; no violation",
  [at("2026-10-25T09:00:00+09:00"), send(addTask, { taskId: "task-1", title: "Buy milk" })],
);
