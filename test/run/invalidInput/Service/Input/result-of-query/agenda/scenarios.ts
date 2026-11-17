import { external, unchecked } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { scenario } from "./agenda.ts";

export const changedByQuery = scenario(
  "Link dayChanged to the query nextDay, which the types reject; test reports resultOfNonCommand and halts, since only a command's request has result events",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: { calendar: external(calendar) } },
    when: (w) => {
      w.net.deliver(w.begin.request(calendar.nextDay));
      w.net.deliver(
        w.peer.calendar.answer(w.begin.request(calendar.nextDay), {
          result: "fulfilled",
          output: { day: "2026-10-25T15:00:00Z" },
        }),
      );
      w.net.deliver(
        w.peer.calendar.emit(calendar.dayChanged, {}, { resultOf: unchecked(w.begin.request(calendar.nextDay)) }),
      );
    },
    then: () => [],
  },
);
