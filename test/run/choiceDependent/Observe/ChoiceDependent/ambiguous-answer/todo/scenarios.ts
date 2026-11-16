import { at, mock, scenario, send } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { addTask, planner } from "./todo.ts";

const firstDay = { result: "fulfilled", output: { day: "2026-10-26T00:00:00+09:00" } } as const;
const secondDay = { result: "fulfilled", output: { day: "2026-10-27T00:00:00+09:00" } } as const;

export const addOne = scenario("Add a task and answer the two requests for the next day in turn; no violation", [
  at("2026-10-25T09:00:00+09:00"),
  send(addTask, { taskId: "task-1", title: "Buy milk" }),
  mock(planner, [calendar.nextDay, firstDay]),
  mock(planner, [calendar.nextDay, secondDay]),
]);
