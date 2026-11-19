import { arm, scenario } from "./tracker.ts";

export const tied = scenario({
  description:
    "Arm at 11:00; the deadlines of first and second tie, and each adds a task with a created key, so test runs both orders. Whichever clock adds first gets Task-1, so the records differ only by a renaming of the created keys, but under that renaming the taskId that watching holds names task a in one order and task b in the other, so test reports stepOrder with the instances",
  given: { start: "2026-10-25T11:00:00+09:00", records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(arm, {});
  },
  then: () => [],
});
