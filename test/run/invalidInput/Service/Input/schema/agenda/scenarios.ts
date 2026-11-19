import { external, fulfilled, rejected } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { scenario } from "./agenda.ts";

export const answerNextDay = scenario({
  description: "Answer the next day; no violation",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [external(calendar)] },
  when: (w) => {
    w.net.deliver(w.startup.request(calendar.nextDay));
    w.net.deliver(
      w.peer.calendar.answer(w.startup.request(calendar.nextDay), fulfilled({ day: "2026-10-26T00:00:00+09:00" })),
    );
  },
  then: () => [],
});

export const rejectNextDay = scenario({
  description: "Reject the next day as unavailable; no violation",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [external(calendar)] },
  when: (w) => {
    w.net.deliver(w.startup.request(calendar.nextDay));
    w.net.deliver(w.peer.calendar.answer(w.startup.request(calendar.nextDay), rejected("unavailable")));
  },
  then: () => [],
});

export const answerMalformedNextDay = scenario({
  description:
    "Answer the next day with a day that is not a datetime; the output schema of nextDay rejects it, so test reports answerOutputSchema",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [external(calendar)] },
  when: (w) => {
    w.net.deliver(w.startup.request(calendar.nextDay));
    w.net.deliver(w.peer.calendar.answer(w.startup.request(calendar.nextDay), fulfilled({ day: "tomorrow" })));
  },
  then: () => [],
});

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
