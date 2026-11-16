import { external } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { scenario } from "./agenda.ts";

export const answerNextDay = scenario("Answer the next day; no violation", {
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: { calendar: external(calendar) } },
  when: (w) => {
    w.net.deliver(w.begin.request(calendar.nextDay));
    w.net.deliver(
      w.peer.calendar.answer(w.begin.request(calendar.nextDay), {
        result: "fulfilled",
        output: { day: "2026-10-26T00:00:00+09:00" },
      }),
    );
  },
  then: () => [],
});

export const rejectNextDay = scenario("Reject the next day as unavailable; no violation", {
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: { calendar: external(calendar) } },
  when: (w) => {
    w.net.deliver(w.begin.request(calendar.nextDay));
    w.net.deliver(
      w.peer.calendar.answer(w.begin.request(calendar.nextDay), {
        result: "rejected",
        rejection: { kind: "unavailable" },
      }),
    );
  },
  then: () => [],
});

export const answerMalformedNextDay = scenario(
  "Answer the next day with a day that is not a datetime; the output schema of nextDay rejects it, so test reports answerOutputSchema",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: { calendar: external(calendar) } },
    when: (w) => {
      w.net.deliver(w.begin.request(calendar.nextDay));
      w.net.deliver(
        w.peer.calendar.answer(w.begin.request(calendar.nextDay), { result: "fulfilled", output: { day: "tomorrow" } }),
      );
    },
    then: () => [],
  },
);

export const rejectNextDayNotFound = scenario(
  "Reject the next day as not-found; nextDay cannot answer with that kind, so test reports unlistedRejectionKind",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: { calendar: external(calendar) } },
    when: (w) => {
      w.net.deliver(w.begin.request(calendar.nextDay));
      w.net.deliver(
        w.peer.calendar.answer(w.begin.request(calendar.nextDay), {
          result: "rejected",
          rejection: { kind: "not-found" },
        }),
      );
    },
    then: () => [],
  },
);
