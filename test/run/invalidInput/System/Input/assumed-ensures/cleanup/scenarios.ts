import { at, mock, scenario } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { remover } from "./cleanup.ts";

export const removeAccepted = scenario(
  "Accept the removal of the reminder before the removal event arrives; test reports failedAssumedEnsures",
  [at("2026-10-25T09:00:00+09:00"), mock(remover, [calendar.removeReminder, { result: "accepted" }])],
);
