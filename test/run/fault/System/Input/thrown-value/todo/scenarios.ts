import { at, call, scenario } from "@natsuzora-dev/tazuna";
import { taskTitle } from "./todo.ts";

export const askMissing = scenario(
  "Ask taskTitle for the title of a missing task; its resolve throws a string, so test reports exception",
  [at("2026-10-25T09:00:00+09:00"), call(taskTitle, { taskId: "task-9" })],
);
