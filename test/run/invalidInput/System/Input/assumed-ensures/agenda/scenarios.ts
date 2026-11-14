import { at, mock, scenario } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { planner } from "./agenda.ts";

export const answer = scenario("Answer a day after from; no violation", [
  at("2026-10-25T09:00:00+09:00"),
  mock(planner, [calendar.nextDay, { result: "fulfilled", output: { day: "2026-10-25T15:00:00Z" } }]),
]);

export const answerBeforeFrom = scenario(
  "Answer a day before from; the answer breaks the assumed ensures afterFrom, so test reports failedAssumedEnsures",
  [
    at("2026-10-25T09:00:00+09:00"),
    mock(planner, [calendar.nextDay, { result: "fulfilled", output: { day: "2026-10-24T15:00:00Z" } }]),
  ],
);
