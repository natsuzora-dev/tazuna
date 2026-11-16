import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./pinger.ts";

export const addOne = scenario(
  "Add a task; sending of pinger writes the transition of pinged as an empty array, so sending is not a state that handles pinged, and receiving pinged does not read sending. Even when the answer to ping exits sending, the receiving step and the answer step do not conflict",
  [at("2026-10-25T09:00:00+09:00"), send(addTask, { taskId: "task-1" })],
);
