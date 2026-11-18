import { arm, scenario } from "./sender.ts";

const given = { start: "2026-10-25T09:00:00+09:00", records: {}, peers: {} } as const;

const when = (w: Parameters<Parameters<typeof scenario>[1]["when"]>[0]) => {
  w.client.send(arm, {});
  w.clock.at("2026-10-25T10:30:00+09:00");
};

export const armAndWait = scenario(
  "Arm and move the clock past 10:00; overdue pongs as soon as it waits, and late pongs at 10:00; the implementation trace keeps that order; no violation",
  { given, when, then: () => [] },
);

export const overduePongFirst = scenario(
  "Arm and move the clock past 10:00; the implementation trace sends overdue's pong before both pings: the deadline follows the step that armed it, which follows overdue's ping, so verify reports lineOrder",
  { given, when, then: () => [] },
);

export const latePongFirst = scenario(
  "Arm and move the clock past 10:00; the implementation trace sends late's 10:00 pong before the 09:00 pings, which the clock line follows, so verify reports lineOrder",
  { given, when, then: () => [] },
);

export const overdueBeforeLate = scenario(
  "Arm and move the clock past 10:00; the implementation trace sends overdue's ping and pong before late's ping: overdue's constant `at` reads nothing that a step writes, so its pong follows only its own ping; no violation",
  { given, when, then: () => [] },
);
