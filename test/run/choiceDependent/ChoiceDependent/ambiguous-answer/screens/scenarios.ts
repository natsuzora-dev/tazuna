import { at, mock, operate, scenario } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { dayScreen } from "./screens.ts";

export const checkOnce = scenario(
  "Check the next day: whichever subscription receives each answer, the outputs stay the same; no violation",
  [
    at("2026-10-25T09:00:00+09:00"),
    operate(dayScreen, "check"),
    mock(dayScreen, [calendar.nextDay, { result: "fulfilled", output: { day: "2026-10-26T00:00:00+09:00" } }]),
    mock(dayScreen, [calendar.nextDay, { result: "fulfilled", output: { day: "2026-10-27T00:00:00+09:00" } }]),
  ],
);
