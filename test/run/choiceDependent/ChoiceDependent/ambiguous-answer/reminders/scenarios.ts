import { at, mock, scenario, send } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { addReminder, scheduler } from "./reminders.ts";

const nextDay = [calendar.nextDay, { result: "fulfilled", output: { day: "2026-10-26T00:00:00+09:00" } }] as const;

export const addSeparately = scenario(
  "Add two reminders in separate sends, so their copies ask in separate messages; no violation",
  [
    at("2026-10-25T09:00:00+09:00"),
    send(addReminder, { reminderId: "reminder-1" }),
    send(addReminder, { reminderId: "reminder-2" }),
    mock(scheduler, nextDay),
    mock(scheduler, nextDay),
  ],
);
