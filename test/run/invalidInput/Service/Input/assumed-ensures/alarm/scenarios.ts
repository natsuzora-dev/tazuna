import { external } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { scenario } from "./alarm.ts";

export const addOnce = scenario({
  description: "The calendar adds the reminder once; no violation",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [external(calendar)] },
  when: (w) => {
    w.net.deliver(w.startup.request(calendar.addReminder));
    w.net.deliver(
      w.peer.calendar.answer(w.startup.request(calendar.addReminder), {
        result: "accepted",
        output: { reminderId: "r-1" },
      }),
    );
    w.net.deliver(
      w.peer.calendar.emit(
        calendar.reminderAdded,
        { reminderId: "r-1" },
        { resultOf: w.startup.request(calendar.addReminder) },
      ),
    );
  },
  then: () => [],
});

export const addTwice = scenario({
  description:
    "Receive reminderAdded twice for one addReminder; this breaks the assumed ensures once, so test reports failedAssumedEnsures",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [external(calendar)] },
  when: (w) => {
    w.net.deliver(w.startup.request(calendar.addReminder));
    w.net.deliver(
      w.peer.calendar.answer(w.startup.request(calendar.addReminder), {
        result: "accepted",
        output: { reminderId: "r-1" },
      }),
    );
    w.net.deliver(
      w.peer.calendar.emit(
        calendar.reminderAdded,
        { reminderId: "r-1" },
        { resultOf: w.startup.request(calendar.addReminder) },
      ),
    );
    w.net.deliver(
      w.peer.calendar.emit(
        calendar.reminderAdded,
        { reminderId: "r-1" },
        { resultOf: w.startup.request(calendar.addReminder) },
      ),
    );
  },
  then: () => [],
});

export const addOther = scenario({
  description:
    "Receive reminderAdded with another id than the answer to addReminder; this breaks the assumed ensures answeredId, so test reports failedAssumedEnsures",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [external(calendar)] },
  when: (w) => {
    w.net.deliver(w.startup.request(calendar.addReminder));
    w.net.deliver(
      w.peer.calendar.answer(w.startup.request(calendar.addReminder), {
        result: "accepted",
        output: { reminderId: "r-1" },
      }),
    );
    w.net.deliver(
      w.peer.calendar.emit(
        calendar.reminderAdded,
        { reminderId: "r-2" },
        { resultOf: w.startup.request(calendar.addReminder) },
      ),
    );
  },
  then: () => [],
});
