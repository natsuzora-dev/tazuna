import { arm, scenario } from "./sender.ts";

const given = { start: "2026-10-25T09:00:00+09:00", records: { Setting: { due: null } }, peers: {} } as const;

const when = (w: Parameters<Parameters<typeof scenario>[1]["when"]>[0]) => {
  w.client.send(arm, {});
};

export const pongAfterDue = scenario(
  "Arm; the automation sets a past due, so the waiter's deadline is overdue at the end of that message and pongs; the implementation trace keeps dueSet before ponged; no violation",
  { given, when, then: () => [] },
);

export const pongBeforeDue = scenario(
  "Arm; the implementation trace sends ponged before dueSet, although the deadline is due only after the write that the step emitting dueSet makes, so verify reports lineOrder",
  { given, when, then: () => [] },
);
