import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./backlog.ts";

export const work = scenario(
  "Add one task and nothing else; no title that the paths of test add starts with Chore, so addTask never emits choreAdded and neither remindChores nor remindOpenChores reacts. test reports automation for both, and nothing about the binding chore or the guard open of remindOpenChores",
  [at("2026-10-25T09:00:00+09:00"), send(addTask, { taskId: "task-1", title: "Buy milk" })],
);
