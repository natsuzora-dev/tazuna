import { at, mock, scenario, send } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { addTask, planner } from "./todo.ts";

export const planAdded = scenario("Plan an added task; no violation", [
  at("2026-10-25T09:00:00+09:00"),
  send(addTask, { taskId: "task-1", title: "Buy milk" }),
  mock(planner, [calendar.nextDay, { result: "fulfilled", output: { day: "2026-10-26T00:00:00+09:00" } }]),
]);

export const answerHoliday = scenario(
  "Plan an added task, but answer calendar.holiday, which the planner never sends; check reports unrequestedAnswer",
  [
    at("2026-10-25T09:00:00+09:00"),
    send(addTask, { taskId: "task-1", title: "Buy milk" }),
    mock(planner, [calendar.holiday, { result: "fulfilled", output: { isHoliday: false } }]),
  ],
);
