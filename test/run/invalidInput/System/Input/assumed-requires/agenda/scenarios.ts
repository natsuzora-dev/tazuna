import { at, mock, scenario } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { todo } from "../todo/contract.ts";
import { planner, reader } from "./agenda.ts";

export const answer = scenario("Answer the start of a day, then reject an hour later with requires; no violation", [
  at("2026-10-25T09:00:00+09:00"),
  mock(planner, [calendar.holiday, { result: "fulfilled", output: { isHoliday: true } }]),
  mock(planner, [calendar.holiday, { result: "rejected", rejection: { kind: "requires", reason: "startOfDay" } }]),
]);

export const rejectUnnamed = scenario("Reject a task with no id with requires; no violation", [
  at("2026-10-25T09:00:00+09:00"),
  mock(reader, [todo.taskTitle, { result: "rejected", rejection: { kind: "requires", reason: "named" } }]),
]);

export const rejectStartOfDay = scenario(
  "Reject the start of a day with requires, then answer an hour later; startOfDay holds for the first and fails for the second, so test reports rejectedAssumedRequires and failedAssumedRequires",
  [
    at("2026-10-25T09:00:00+09:00"),
    mock(planner, [calendar.holiday, { result: "rejected", rejection: { kind: "requires", reason: "startOfDay" } }]),
    mock(planner, [calendar.holiday, { result: "fulfilled", output: { isHoliday: true } }]),
  ],
);

export const answerUnnamed = scenario(
  "Answer the title of a task with no id; this breaks the assumed requires named, so test reports failedAssumedRequires",
  [
    at("2026-10-25T09:00:00+09:00"),
    mock(reader, [todo.taskTitle, { result: "fulfilled", output: { title: "Buy milk" } }]),
  ],
);
