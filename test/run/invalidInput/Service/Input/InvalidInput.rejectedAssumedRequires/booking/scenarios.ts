import { external, rejected } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { scenario } from "./booking.ts";

export const rejectBookingAtStartOfDay = scenario({
  description:
    "Reject a booking at the start of a day with requires; startOfDay holds, so test reports rejectedAssumedRequires",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [external(calendar)] },
  when: (w) => {
    w.net.deliver(w.startup.request(calendar.book));
    w.net.deliver(w.peer.calendar.answer(w.startup.request(calendar.book), rejected("requires", "startOfDay")));
  },
  then: () => [],
});
