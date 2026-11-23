import { parseInstant } from "@natsuzora-dev/tazuna";
import { arm, scenario } from "./tokens.ts";

export const tied = scenario({
  description:
    "Arm at 11:00; the deadlines of first and second tie. first clears Last.id and second sets it to a created key, so the order that runs second last leaves the created key and the other leaves the empty string. Last.id reuses the key field of Note, a key position, but a created key never stands for the empty string, so test reports stepOrder",
  given: { start: parseInstant("2026-10-25T11:00:00+09:00"), records: { Note: [], Last: { id: "" } }, peers: [] },
  when: (w) => {
    w.client.as("client").send(arm, {});
  },
  then: () => [],
});
