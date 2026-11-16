import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTwoTasks } from "./notes.ts";

export const addTwo = scenario(
  "Add two tasks in one command; noteOnTask labels both notes note, so test reports repeatedKeyLabel of noteOnTask",
  [at("2026-10-25T09:00:00+09:00"), send(addTwoTasks, { first: "task-1", second: "task-2" })],
);
