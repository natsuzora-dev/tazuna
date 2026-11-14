import { at, mock, scenario } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { planner } from "./agenda.ts";

export const answer = scenario("Answer the start of a day, then reject an hour later with requires; no violation", [
  at("2026-10-25T09:00:00+09:00"),
  mock(planner, [calendar.holiday, { result: "fulfilled", output: { isHoliday: true } }]),
  mock(planner, [calendar.holiday, { result: "rejected", rejection: { kind: "requires", reason: "startOfDay" } }]),
]);

export const rejectStartOfDay = scenario(
  "Reject the start of a day with requires, then answer an hour later; startOfDay holds for the first and fails for the second, so test reports rejectedAssumedRequires and failedAssumedRequires",
  [
    at("2026-10-25T09:00:00+09:00"),
    mock(planner, [calendar.holiday, { result: "rejected", rejection: { kind: "requires", reason: "startOfDay" } }]),
    mock(planner, [calendar.holiday, { result: "fulfilled", output: { isHoliday: true } }]),
  ],
);
