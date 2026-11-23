import { parseInstant } from "@natsuzora-dev/tazuna";
import { arm, given, scenario } from "./sender.ts";

const arranged = given({ start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [] });

const when = arranged.step((w) => {
  w.client.as("client").send(arm, {});
  w.clock.at(parseInstant("2026-10-25T10:30:00+09:00"));
});

export const armAndWait = scenario({
  description:
    "Arm and move the clock past 10:00; overdue pongs as soon as it waits, and late pongs at 10:00; the implementation trace keeps that order; no violation",
  given: arranged,
  when,
  then: () => [],
});

export const overduePongFirst = scenario({
  description:
    "Arm and move the clock past 10:00; the implementation trace sends overdue's pong before both pings: the deadline follows the step that armed it, which follows overdue's ping, so verify reports lineOrder",
  given: arranged,
  when,
  then: () => [],
});

export const latePongFirst = scenario({
  description:
    "Arm and move the clock past 10:00; the implementation trace sends late's 10:00 pong before the 09:00 pings, which the clock line follows, so verify reports lineOrder",
  given: arranged,
  when,
  then: () => [],
});

export const overdueBeforeLate = scenario({
  description:
    "Arm and move the clock past 10:00; the implementation trace sends overdue's ping and pong before late's ping: a deadline follows only the step that entered its state, so overdue's pong follows only its own ping; no violation",
  given: arranged,
  when,
  then: () => [],
});
