import { external } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { scenario } from "./cleanup.ts";

export const removeAccepted = scenario(
  "Accept the removal of the reminder before the removal event arrives; test reports failedAssumedEnsures",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: { calendar: external(calendar) } },
    when: (w) => {
      w.net.deliver(w.begin.request(calendar.removeReminder));
      w.net.deliver(w.peer.calendar.answer(w.begin.request(calendar.removeReminder), { result: "accepted" }));
    },
    then: () => [],
  },
);
