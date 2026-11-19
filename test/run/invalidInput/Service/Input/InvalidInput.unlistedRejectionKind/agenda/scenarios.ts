import { external, rejected } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { scenario } from "./agenda.ts";

export const rejectNextDayNotFound = scenario({
  description:
    "Reject the next day as not-found; nextDay cannot answer with that kind, so test reports unlistedRejectionKind",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [external(calendar)] },
  when: (w) => {
    w.net.deliver(w.startup.request(calendar.nextDay));
    w.net.deliver(w.peer.calendar.answer(w.startup.request(calendar.nextDay), rejected("not-found")));
  },
  then: () => [],
});
