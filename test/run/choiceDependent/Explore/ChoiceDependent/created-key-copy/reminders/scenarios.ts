import { arm, scenario } from "./reminders.ts";

export const tied = scenario({
  description:
    "Arm at 11:00; the deadlines of first and second tie, and each adds a task with a created key, so test runs both orders. Whichever clock adds first gets Task-1, so the records and the reminder copies, keyed by taskId, differ only by a renaming of the created keys, and test reports nothing",
  given: { start: "2026-10-25T11:00:00+09:00", records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(arm, {});
  },
  then: () => [],
});
