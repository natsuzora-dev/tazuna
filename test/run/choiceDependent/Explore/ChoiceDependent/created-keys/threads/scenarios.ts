import { arm, scenario } from "./threads.ts";

export const swappedKeys = scenario(
  "Arm at 11:00; the deadlines of first and second tie. Whichever clock posts first gets the lower Note keys, so the two orders differ only by a renaming of the created keys, and each reply names its own note in both, so test reports nothing",
  {
    given: { start: "2026-10-25T11:00:00+09:00", records: { Note: [] }, peers: {} },
    when: (w) => {
      w.client.send(arm, {});
    },
    then: () => [],
  },
);
