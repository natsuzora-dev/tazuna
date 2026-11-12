import { at, call, scenario } from "@natsuzora-dev/tazuna";
import { taskCount } from "./todo.ts";

export const countNone = scenario(
  "Count the tasks while there is none; the refinement of the output schema of taskCount throws, so test reports exception of taskCount",
  [at("2026-10-25T09:00:00+09:00"), call(taskCount, {})],
);
