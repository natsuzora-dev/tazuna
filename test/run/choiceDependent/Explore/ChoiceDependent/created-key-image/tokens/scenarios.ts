import { arm, scenario } from "./tokens.ts";

export const tied = scenario(
  "Arm at 11:00; the deadlines of first and second tie. first clears Last.id and second sets it to a created key, so the order that runs second last leaves the created key and the other leaves the empty string. Last.id is a plain z.string(), so the two compare as text and test reports stepOrder",
  {
    given: { start: "2026-10-25T11:00:00+09:00", records: { Note: [], Last: { id: "" } }, peers: {} },
    when: (w) => {
      w.client.send(arm, {});
    },
    then: () => [],
  },
);
