import { external, fulfilled, parseInstant, rejected } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { scenario } from "./agenda.ts";

export const answer = scenario({
  description: "Answer the start of a day, then reject an hour later with requires; no violation",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [external(calendar)] },
  when: (w) => {
    w.net.deliver(w.startup.request(calendar.holiday));
    const l0 = w.net.deliver(
      w.peer.calendar.answer(w.startup.request(calendar.holiday), fulfilled({ isHoliday: true })),
    );
    w.net.deliver(l0.request(calendar.holiday));
    w.net.deliver(w.peer.calendar.answer(l0.request(calendar.holiday), rejected("requires", "startOfDay")));
  },
  then: () => [],
});

export const rejectStartOfDay = scenario({
  description:
    "Reject the start of a day with requires, then answer an hour later; startOfDay holds for the first and fails for the second, so test reports rejectedAssumedRequires and failedAssumedRequires",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [external(calendar)] },
  when: (w) => {
    w.net.deliver(w.startup.request(calendar.holiday));
    const l0 = w.net.deliver(
      w.peer.calendar.answer(w.startup.request(calendar.holiday), rejected("requires", "startOfDay")),
    );
    w.net.deliver(l0.request(calendar.holiday));
    w.net.deliver(w.peer.calendar.answer(l0.request(calendar.holiday), fulfilled({ isHoliday: true })));
  },
  then: () => [],
});
