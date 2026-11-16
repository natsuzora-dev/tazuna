import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./todo.ts";

export const addTwoWithOneTag = scenario("Add two tasks with one tag; test reports duplicateItemKey", [
  at("2026-10-25T09:00:00+09:00"),
  send(addTask, { taskId: "task-1", tag: "home" }),
  send(addTask, { taskId: "task-2", tag: "home" }),
]);
