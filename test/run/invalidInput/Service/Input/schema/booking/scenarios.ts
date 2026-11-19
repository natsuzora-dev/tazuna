import { accepted, external } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { scenario } from "./booking.ts";

export const answerBooking = scenario({
  description: "Answer the booking with its id; no violation",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [external(calendar)] },
  when: (w) => {
    w.net.deliver(w.startup.request(calendar.book));
    w.net.deliver(w.peer.calendar.answer(w.startup.request(calendar.book), accepted({ bookingId: "booking-1" })));
  },
  then: () => [],
});

export const answerBookingEmptyId = scenario({
  description:
    "Answer the booking with an empty id; the output schema of book rejects it, so test reports answerOutputSchema",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [external(calendar)] },
  when: (w) => {
    w.net.deliver(w.startup.request(calendar.book));
    w.net.deliver(w.peer.calendar.answer(w.startup.request(calendar.book), accepted({ bookingId: "" })));
  },
  then: () => [],
});
