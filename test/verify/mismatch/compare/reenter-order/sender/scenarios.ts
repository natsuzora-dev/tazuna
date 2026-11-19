import { arm, scenario } from "./sender.ts";

const given = { start: "2026-10-25T09:00:00+09:00", records: { Setting: { due: null } }, peers: [] } as const;

const when = (w: Parameters<Parameters<typeof scenario>[1]["when"]>[0]) => {
  w.client.send(arm, {});
};

export const pongAfterDue = scenario(
  "Arm; the automation sets a past due, and the waiter enters waiting again on dueChanged, so its deadline is overdue and pongs; the implementation trace keeps dueSet before ponged; no violation",
  { given, when, then: () => [] },
);

export const pongBeforeDue = scenario(
  "Arm; the implementation trace sends ponged before dueSet, although the deadline follows the step that entered waiting again, which the step emitting dueSet caused, so verify reports lineOrder",
  { given, when, then: () => [] },
);
