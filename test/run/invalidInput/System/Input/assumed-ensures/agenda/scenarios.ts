import { at, mock, scenario } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { todo } from "../todo/contract.ts";
import { planner, reader } from "./agenda.ts";

export const answer = scenario("Answer a day after from; no violation", [
  at("2026-10-25T09:00:00+09:00"),
  mock(planner, [calendar.nextDay, { result: "fulfilled", output: { day: "2026-10-25T15:00:00Z" } }]),
]);

export const readTitles = scenario("Answer two different titles; no violation", [
  at("2026-10-25T09:00:00+09:00"),
  mock(reader, [todo.taskTitles, { result: "fulfilled", output: { titles: ["Buy bread", "Buy milk"] } }]),
]);

export const answerBeforeFrom = scenario(
  "Answer a day before from; the answer breaks the assumed ensures afterFrom, so test reports failedAssumedEnsures",
  [
    at("2026-10-25T09:00:00+09:00"),
    mock(planner, [calendar.nextDay, { result: "fulfilled", output: { day: "2026-10-24T15:00:00Z" } }]),
  ],
);

export const readTitleTwice = scenario(
  "Answer one title twice; the answer breaks the assumed ensures distinct, so test reports failedAssumedEnsures",
  [
    at("2026-10-25T09:00:00+09:00"),
    mock(reader, [todo.taskTitles, { result: "fulfilled", output: { titles: ["Buy milk", "Buy milk"] } }]),
  ],
);
