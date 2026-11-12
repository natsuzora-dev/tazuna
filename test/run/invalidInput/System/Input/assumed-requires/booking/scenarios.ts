import { at, mock, receive, scenario } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { booker } from "./booking.ts";

const accepted = mock(booker, [calendar.book, { result: "accepted" }]);

export const acceptBookingLater = scenario(
  "Accept a booking an hour after the start of a day; this breaks the assumed requires startOfDay, so test reports failedAssumedRequires and does not check the booked event of another day against the assumed ensures sameDay",
  [
    at("2026-10-25T10:00:00+09:00"),
    accepted,
    receive(calendar.booked, { day: "2026-10-26T00:00:00Z" }, { resultOf: accepted }),
  ],
);

export const rejectBookingAtStartOfDay = scenario(
  "Reject a booking at the start of a day with requires; startOfDay holds, so test reports rejectedAssumedRequires",
  [
    at("2026-10-25T09:00:00+09:00"),
    mock(booker, [calendar.book, { result: "rejected", rejection: { kind: "requires", reason: "startOfDay" } }]),
  ],
);
