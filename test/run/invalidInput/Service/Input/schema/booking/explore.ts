import { domain, explore } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";

export const bookingExplore = explore({
  service: "booking",
  depth: 2,
  domains: [domain(calendar.book.output.bookingId, ["booking-1"])],
});
