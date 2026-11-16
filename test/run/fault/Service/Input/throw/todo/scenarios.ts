import { at, call, scenario } from "@natsuzora-dev/tazuna";
import { taskTitle } from "./todo.ts";

export const askMissing = scenario("Ask for the title of a missing task; taskTitle answers null; no violation", [
  at("2026-10-25T09:00:00+09:00"),
  call(taskTitle, { taskId: "task-9" }),
]);
