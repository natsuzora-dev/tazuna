import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { starTask } from "./stars.ts";

export const keyOutOfSchema = scenario(
  "Star the task other-1; taskStarred, whose payload taskId does not fit the key schema, reaches no copy, and no copy marks",
  [at("2026-10-25T10:00:00+09:00"), send(starTask, { taskId: "other-1" })],
);
