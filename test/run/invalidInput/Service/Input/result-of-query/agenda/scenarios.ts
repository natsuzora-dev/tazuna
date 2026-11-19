import { external, fulfilled, unchecked } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { scenario } from "./agenda.ts";

export const changedByQuery = scenario(
  "Link dayChanged to the query nextDay, which the types reject; test reports resultOfNonCommand when the run ends, since only a command's request has result events",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [external(calendar)] },
    when: (w) => {
      w.net.deliver(w.startup.request(calendar.nextDay));
      w.net.deliver(
        w.peer.calendar.answer(w.startup.request(calendar.nextDay), fulfilled({ day: "2026-10-25T15:00:00Z" })),
      );
      w.net.deliver(
        w.peer.calendar.emit(calendar.dayChanged, {}, { resultOf: unchecked(w.startup.request(calendar.nextDay)) }),
      );
    },
    then: () => [],
  },
);
