import { at, mock, scenario } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { booker } from "./booking.ts";

export const answerBooking = scenario("Answer the booking with its id; no violation", [
  at("2026-10-25T09:00:00+09:00"),
  mock(booker, [calendar.book, { result: "accepted", output: { bookingId: "booking-1" } }]),
]);

export const answerBookingEmptyId = scenario(
  "Answer the booking with an empty id; the output schema of book rejects it, so test reports answerOutputSchema",
  [at("2026-10-25T09:00:00+09:00"), mock(booker, [calendar.book, { result: "accepted", output: { bookingId: "" } }])],
);
