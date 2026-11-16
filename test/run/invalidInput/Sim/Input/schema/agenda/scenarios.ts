import { at, mock, scenario } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { agenda } from "./agenda.ts";

export const answerNextDay = scenario("Answer the next day; no violation", [
  at("2026-10-25T09:00:00+09:00"),
  mock(agenda, [calendar.nextDay, { result: "fulfilled", output: { day: "2026-10-26T00:00:00+09:00" } }]),
]);

export const rejectNextDay = scenario("Reject the next day as unavailable; no violation", [
  at("2026-10-25T09:00:00+09:00"),
  mock(agenda, [calendar.nextDay, { result: "rejected", rejection: { kind: "unavailable" } }]),
]);

export const answerMalformedNextDay = scenario(
  "Answer the next day with a day that is not a datetime; the output schema of nextDay rejects it, so test reports answerOutputSchema",
  [
    at("2026-10-25T09:00:00+09:00"),
    mock(agenda, [calendar.nextDay, { result: "fulfilled", output: { day: "tomorrow" } }]),
  ],
);

export const rejectNextDayNotFound = scenario(
  "Reject the next day as not-found; nextDay cannot answer with that kind, so test reports unlistedRejectionKind",
  [
    at("2026-10-25T09:00:00+09:00"),
    mock(agenda, [calendar.nextDay, { result: "rejected", rejection: { kind: "not-found" } }]),
  ],
);
