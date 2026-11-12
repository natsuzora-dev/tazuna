import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./todo.ts";

export const addOne = scenario(
  "Add a task; addTask decides taskRemoved, whose payload matches taskAdded's but which its emits do not list, so test reports unlistedEmittedEvent",
  [at("2026-10-25T09:00:00+09:00"), send(addTask, { taskId: "task-1" })],
);
