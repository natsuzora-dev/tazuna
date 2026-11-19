import { arm, given, scenario } from "./sender.ts";

const arranged = given({ start: "2026-10-25T09:00:00+09:00", records: { Setting: { due: null } }, peers: [] });

const when = arranged.step((w) => {
  w.client.send(arm, {});
});

export const pongAfterDue = scenario({
  description:
    "Arm; the automation sets a past due, and the waiter enters waiting again on dueChanged, so its deadline is overdue and pongs; the implementation trace keeps dueSet before ponged; no violation",
  given: arranged,
  when,
  then: () => [],
});

export const pongBeforeDue = scenario({
  description:
    "Arm; the implementation trace sends ponged before dueSet, although the deadline follows the step that entered waiting again, which the step emitting dueSet caused, so verify reports lineOrder",
  given: arranged,
  when,
  then: () => [],
});
