import { at, mock, scenario, send } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { perTask } from "./machines.ts";
import { addTask } from "./todo.ts";

const nextDay = { result: "fulfilled", output: { day: "2026-10-26T00:00:00+09:00" } } as const;

export const answerToReplacedCopy = scenario(
  "Add task-1 at 10:00 and answer twice at 11:00; the copy of task-1 enters asking and sends calendar.nextDay#1. The request is not stale yet when the answer arrives, so the mock has no stale. perTask reenters rows through an always transition before it processes the answer, so the copy of task-1 ends, calendar.nextDay#1 becomes stale, and a new copy of the same key enters asking. The answer to the stale request does not reach the new copy, so the new copy stays in asking and sends calendar.nextDay#2, which the second mock answers",
  [
    at("2026-10-25T10:00:00+09:00"),
    send(addTask, { taskId: "task-1" }),
    at("2026-10-25T11:00:00+09:00"),
    mock(perTask, [calendar.nextDay, nextDay]),
    mock(perTask, [calendar.nextDay, nextDay]),
  ],
);
