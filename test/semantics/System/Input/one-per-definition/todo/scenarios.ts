import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./todo.ts";

export const oneGreeter = scenario(
  "Add two tasks; only one greeter starts, at 10:00 when todo starts, and greets for the first time, and the same greeter counts up and greets on each addTask",
  [at("2026-10-25T10:00:00+09:00"), send(addTask, { taskId: "task-1" }), send(addTask, { taskId: "task-2" })],
);
