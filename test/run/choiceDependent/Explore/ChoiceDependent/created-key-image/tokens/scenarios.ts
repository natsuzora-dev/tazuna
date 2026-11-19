import { arm, scenario } from "./tokens.ts";

export const tied = scenario(
  "Arm at 11:00; the deadlines of first and second tie. first clears Last.id and second sets it to a created key, so the order that runs second last leaves the created key and the other leaves the empty string. Last.id reuses the key field of Note, a key position, but a created key never stands for the empty string, so test reports stepOrder",
  {
    given: { start: "2026-10-25T11:00:00+09:00", records: { Note: [], Last: { id: "" } }, peers: [] },
    when: (w) => {
      w.client.send(arm, {});
    },
    then: () => [],
  },
);
