import { external } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { scenario } from "./agenda.ts";

export const answer = scenario("Answer the start of a day, then reject an hour later with requires; no violation", {
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: { calendar: external(calendar) } },
  when: (w) => {
    w.net.deliver(w.begin.request(calendar.holiday));
    const l0 = w.net.deliver(
      w.peer.calendar.answer(w.begin.request(calendar.holiday), { result: "fulfilled", output: { isHoliday: true } }),
    );
    w.net.deliver(l0.request(calendar.holiday));
    w.net.deliver(
      w.peer.calendar.answer(l0.request(calendar.holiday), {
        result: "rejected",
        rejection: { kind: "requires", reason: "startOfDay" },
      }),
    );
  },
  then: () => [],
});

export const rejectStartOfDay = scenario(
  "Reject the start of a day with requires, then answer an hour later; startOfDay holds for the first and fails for the second, so test reports rejectedAssumedRequires and failedAssumedRequires",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: { calendar: external(calendar) } },
    when: (w) => {
      w.net.deliver(w.begin.request(calendar.holiday));
      const l0 = w.net.deliver(
        w.peer.calendar.answer(w.begin.request(calendar.holiday), {
          result: "rejected",
          rejection: { kind: "requires", reason: "startOfDay" },
        }),
      );
      w.net.deliver(l0.request(calendar.holiday));
      w.net.deliver(
        w.peer.calendar.answer(l0.request(calendar.holiday), { result: "fulfilled", output: { isHoliday: true } }),
      );
    },
    then: () => [],
  },
);
