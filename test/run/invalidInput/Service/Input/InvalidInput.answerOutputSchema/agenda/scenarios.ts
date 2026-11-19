import { external, fulfilled } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { scenario } from "./agenda.ts";

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
