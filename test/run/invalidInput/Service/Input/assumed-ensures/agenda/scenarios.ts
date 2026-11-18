import { external } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { scenario } from "./agenda.ts";

export const answer = scenario("Answer a day after from; no violation", {
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: { calendar: external(calendar) } },
  when: (w) => {
    w.net.deliver(w.startup.request(calendar.nextDay));
    w.net.deliver(
      w.peer.calendar.answer(w.startup.request(calendar.nextDay), {
        result: "fulfilled",
        output: { day: "2026-10-25T15:00:00Z" },
      }),
    );
  },
  then: () => [],
});

export const answerBeforeFrom = scenario(
  "Answer a day before from; the answer breaks the assumed ensures afterFrom, so test reports failedAssumedEnsures when the run ends",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: { calendar: external(calendar) } },
    when: (w) => {
      w.net.deliver(w.startup.request(calendar.nextDay));
      w.net.deliver(
        w.peer.calendar.answer(w.startup.request(calendar.nextDay), {
          result: "fulfilled",
          output: { day: "2026-10-24T15:00:00Z" },
        }),
      );
    },
    then: () => [],
  },
);

export const answerBeforeFromAfterRestart = scenario(
  "Restart while calendar holds nextDay, then answer it a day before from; no request waits for the answer, so it changes nothing, but the end of the run checks every answer that arrived, and test reports failedAssumedEnsures",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: { calendar: external(calendar) } },
    when: (w) => {
      const first = w.startup.request(calendar.nextDay);
      w.net.deliver(first);
      const second = w.host.restart().request(calendar.nextDay);
      w.net.deliver(second);
      w.peer.calendar.leaveUnanswered(second);
      w.net.deliver(w.peer.calendar.answer(first, { result: "fulfilled", output: { day: "2026-10-24T15:00:00Z" } }));
    },
    then: () => [],
  },
);
