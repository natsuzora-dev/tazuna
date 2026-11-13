import { at, mock, scenario, send } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { addTask, planner } from "./todo.ts";

const day = (time: string) => mock(planner, [calendar.nextDay, { result: "fulfilled", output: { day: time } }]);

export const addTwo = scenario("Add two tasks an hour apart, and get the next day for each; no violation", [
  at("2026-10-25T00:00:00Z"),
  send(addTask, { taskId: "task-1", title: "Buy milk" }),
  day("2026-10-26T00:00:00Z"),
  at("2026-10-25T01:00:00Z"),
  send(addTask, { taskId: "task-2", title: "Buy eggs" }),
  day("2026-10-26T01:00:00Z"),
]);

export const addTwoReusedId = scenario(
  "Add two tasks an hour apart, and get the next day for the first; the implementation trace of this scenario gives the second calendar.nextDay request the id of the first, so verify reports Mismatch.renaming",
  [
    at("2026-10-25T00:00:00Z"),
    send(addTask, { taskId: "task-1", title: "Buy milk" }),
    day("2026-10-26T00:00:00Z"),
    at("2026-10-25T01:00:00Z"),
    send(addTask, { taskId: "task-2", title: "Buy eggs" }),
  ],
);

export const addOneOwnAnswer = scenario(
  "Add a task; the implementation trace of this scenario gives its calendar.nextDay request the id of the addTask command, so that its answer to addTask also names its own request, and verify reports Mismatch.renaming",
  [at("2026-10-25T00:00:00Z"), send(addTask, { taskId: "task-1", title: "Buy milk" })],
);
