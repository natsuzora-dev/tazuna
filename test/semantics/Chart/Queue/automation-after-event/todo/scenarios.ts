import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./todo.ts";

export const addTwice = scenario(
  "Add two tasks; countAdded reacts after taskAdded is applied to the records, so it reports 1 after the first addTask and 2 after the second",
  [at("2026-10-25T10:00:00+09:00"), send(addTask, { taskId: "task-1" }), send(addTask, { taskId: "task-2" })],
);
