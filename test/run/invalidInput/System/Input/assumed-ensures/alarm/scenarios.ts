import { at, mock, receive, scenario } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { reminder } from "./alarm.ts";

const added = mock(reminder, [calendar.addReminder, { result: "accepted", output: { reminderId: "r-1" } }]);

export const addOnce = scenario("The calendar adds the reminder once; no violation", [
  at("2026-10-25T09:00:00+09:00"),
  added,
  receive(calendar.reminderAdded, { reminderId: "r-1" }, { resultOf: added }),
]);

export const addTwice = scenario(
  "Receive reminderAdded twice for one addReminder; this breaks the assumed ensures once, so test reports failedAssumedEnsures",
  [
    at("2026-10-25T09:00:00+09:00"),
    added,
    receive(calendar.reminderAdded, { reminderId: "r-1" }, { resultOf: added }),
    receive(calendar.reminderAdded, { reminderId: "r-1" }, { resultOf: added }),
  ],
);

const addedOther = mock(reminder, [calendar.addReminder, { result: "accepted", output: { reminderId: "r-1" } }]);

export const addOther = scenario(
  "Receive reminderAdded with another id than the answer to addReminder; this breaks the assumed ensures answeredId, so test reports failedAssumedEnsures",
  [
    at("2026-10-25T09:00:00+09:00"),
    addedOther,
    receive(calendar.reminderAdded, { reminderId: "r-2" }, { resultOf: addedOther }),
  ],
);
