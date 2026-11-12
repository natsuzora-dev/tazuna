import { at, mock, operate, scenario } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { dayScreen } from "./screens.ts";

const day = { result: "fulfilled", output: { day: "2026-10-26T00:00:00+09:00" } } as const;

export const checkOnceAndAdd = scenario(
  "Check the next day; the first answer can go to either subscription, and then whether the task is added changes, so test reports answerChoice and answerOrder",
  [
    at("2026-10-25T09:00:00+09:00"),
    operate(dayScreen, "check"),
    mock(dayScreen, [calendar.nextDay, day]),
    mock(dayScreen, [calendar.nextDay, day]),
  ],
);
