import { external, fulfilled, parseInstant } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { scenario } from "./agenda.ts";

export const answerMalformedNextDay = scenario({
  description:
    "Answer the next day with a day that is no whole millisecond; the output schema of nextDay rejects it, so test reports answerOutputSchema",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [external(calendar)] },
  when: (w) => {
    w.net.deliver(w.startup.request(calendar.nextDay));
    w.net.deliver(w.peer.calendar.answer(w.startup.request(calendar.nextDay), fulfilled({ day: 1.5 })));
  },
  then: () => [],
});
