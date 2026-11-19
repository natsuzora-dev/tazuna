import { accepted, external } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { scenario } from "./cleanup.ts";

export const removeAccepted = scenario(
  "Accept the removal of the reminder, and no removal event arrives before the run ends; the assumed ensures removedOnce is checked once at the end with all result events, so test reports failedAssumedEnsures",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [external(calendar)] },
    when: (w) => {
      w.net.deliver(w.startup.request(calendar.removeReminder));
      w.net.deliver(w.peer.calendar.answer(w.startup.request(calendar.removeReminder), accepted));
    },
    then: () => [],
  },
);

export const removedAfterAnswer = scenario(
  "Accept the removal of the reminder, then the removal event arrives; the assumed ensures removedOnce is checked at the end of the run, when the event has arrived, so no violation",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [external(calendar)] },
    when: (w) => {
      const removing = w.startup.request(calendar.removeReminder);
      w.net.deliver(removing);
      w.net.deliver(w.peer.calendar.answer(removing, accepted));
      w.net.deliver(w.peer.calendar.emit(calendar.reminderRemoved, {}, { resultOf: removing }));
    },
    then: () => [],
  },
);
