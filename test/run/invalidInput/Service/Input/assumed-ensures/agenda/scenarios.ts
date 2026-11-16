import { external } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { scenario } from "./agenda.ts";

export const answer = scenario("Answer a day after from; no violation", {
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: { calendar: external(calendar) } },
  when: (w) => {
    w.net.deliver(w.begin.request(calendar.nextDay));
    w.net.deliver(
      w.peer.calendar.answer(w.begin.request(calendar.nextDay), {
        result: "fulfilled",
        output: { day: "2026-10-25T15:00:00Z" },
      }),
    );
  },
  then: () => [],
});

export const answerBeforeFrom = scenario(
  "Answer a day before from; the answer breaks the assumed ensures afterFrom, so test reports failedAssumedEnsures",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: { calendar: external(calendar) } },
    when: (w) => {
      w.net.deliver(w.begin.request(calendar.nextDay));
      w.net.deliver(
        w.peer.calendar.answer(w.begin.request(calendar.nextDay), {
          result: "fulfilled",
          output: { day: "2026-10-24T15:00:00Z" },
        }),
      );
    },
    then: () => [],
  },
);
