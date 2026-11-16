import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./echo.ts";

export const addTwo = scenario(
  "Add two tasks: each message passes a chain of 100 commands, and the count of the chain starts again for the second message; no violation",
  [at("2026-10-25T09:00:00+09:00"), send(addTask, { taskId: "task-1" }), send(addTask, { taskId: "task-2" })],
);
