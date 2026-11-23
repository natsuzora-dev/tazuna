import { accepted, external, parseInstant, rejected } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { scenario } from "./booking.ts";

export const acceptBookingLater = scenario({
  description:
    "Accept a booking an hour after the start of a day; this breaks the assumed requires startOfDay, so test reports failedAssumedRequires and does not check the booked event of another day against the assumed ensures sameDay",
  given: { start: parseInstant("2026-10-25T10:00:00+09:00"), records: {}, peers: [external(calendar)] },
  when: (w) => {
    w.net.deliver(w.startup.request(calendar.book));
    w.net.deliver(w.peer.calendar.answer(w.startup.request(calendar.book), accepted()));
    w.net.deliver(
      w.peer.calendar.emit(
        calendar.booked,
        { day: parseInstant("2026-10-26T00:00:00Z") },
        { resultOf: w.startup.request(calendar.book) },
      ),
    );
  },
  then: () => [],
});

export const rejectBookingAtStartOfDay = scenario({
  description:
    "Reject a booking at the start of a day with requires; startOfDay holds, so test reports rejectedAssumedRequires",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [external(calendar)] },
  when: (w) => {
    w.net.deliver(w.startup.request(calendar.book));
    w.net.deliver(w.peer.calendar.answer(w.startup.request(calendar.book), rejected("requires", "startOfDay")));
  },
  then: () => [],
});
