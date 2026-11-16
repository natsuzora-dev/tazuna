import { at, mock, scenario, send } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { planner } from "./machines.ts";
import { addTask } from "./todo.ts";

export const answerAfterAlways = scenario(
  "Add a task at 10:00 and answer at 12:00; planner enters asking and sends calendar.nextDay. The request is not stale yet when the answer arrives, so the mock has no stale. planner evaluates its always guards before it processes the answer and enters gaveUp, so the answer takes no onFulfilled transition and planner sends no noteAnswer",
  [
    at("2026-10-25T10:00:00+09:00"),
    send(addTask, { taskId: "task-1" }),
    at("2026-10-25T12:00:00+09:00"),
    mock(planner, [calendar.nextDay, { result: "fulfilled", output: { day: "2026-10-26T00:00:00+09:00" } }]),
  ],
);
