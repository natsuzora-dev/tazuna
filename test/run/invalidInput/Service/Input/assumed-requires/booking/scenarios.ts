import { external } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { scenario } from "./booking.ts";

export const acceptBookingLater = scenario(
  "Accept a booking an hour after the start of a day; this breaks the assumed requires startOfDay, so test reports failedAssumedRequires and does not check the booked event of another day against the assumed ensures sameDay",
  {
    given: { start: "2026-10-25T10:00:00+09:00", records: {}, peers: { calendar: external(calendar) } },
    when: (w) => {
      w.net.deliver(w.begin.request(calendar.book));
      w.net.deliver(w.peer.calendar.answer(w.begin.request(calendar.book), { result: "accepted" }));
      w.net.deliver(
        w.peer.calendar.emit(
          calendar.booked,
          { day: "2026-10-26T00:00:00Z" },
          { resultOf: w.begin.request(calendar.book) },
        ),
      );
    },
    then: () => [],
  },
);

export const rejectBookingAtStartOfDay = scenario(
  "Reject a booking at the start of a day with requires; startOfDay holds, so test reports rejectedAssumedRequires",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: { calendar: external(calendar) } },
    when: (w) => {
      w.net.deliver(w.begin.request(calendar.book));
      w.net.deliver(
        w.peer.calendar.answer(w.begin.request(calendar.book), {
          result: "rejected",
          rejection: { kind: "requires", reason: "startOfDay" },
        }),
      );
    },
    then: () => [],
  },
);
