import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./backlog.ts";

export const work = scenario(
  "Add one task and nothing else. The task that taskAdded names always exists, so completeChores never binds added to null; no title that the paths of test add starts with Chore, so the guard chore is never true; and the paths add no second task, so completeDuplicates never binds earlier to a value. test reports automationBindingNull, automationGuard, and automationBindingValue",
  [at("2026-10-25T09:00:00+09:00"), send(addTask, { taskId: "task-1", title: "Buy milk" })],
);
