import { parseInstant } from "@natsuzora-dev/tazuna";
import { arm, scenario } from "./replies.ts";

export const replyToEarlier = scenario({
  description:
    "Arm at 11:00; the deadlines of first and second tie. The clock that posts second replies to the other's note, so no renaming of the created keys makes the two orders' records equal, and test reports stepOrder",
  given: { start: parseInstant("2026-10-25T11:00:00+09:00"), records: { Note: [], Last: { id: null } }, peers: [] },
  when: (w) => {
    w.client.as("client").send(arm, {});
  },
  then: () => [],
});
