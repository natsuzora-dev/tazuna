import { arm, scenario } from "./replies.ts";

export const replyToEarlier = scenario(
  "Arm at 11:00; the deadlines of first and second tie. The clock that posts second replies to the other's note, so no renaming of the created keys makes the two orders' records equal, and test reports stepOrder",
  {
    given: { start: "2026-10-25T11:00:00+09:00", records: { Note: [], Last: { id: null } }, peers: {} },
    when: (w) => {
      w.client.send(arm, {});
    },
    then: () => [],
  },
);
