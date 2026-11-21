import { domain, explore } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";

export const alarmExplore = explore({
  service: "alarm",
  depth: 2,
  domains: [
    domain(calendar.addReminder.output.reminderId, ["r-1"]),
    domain(calendar.reminderAdded.payload.reminderId, ["r-1"]),
  ],
});
