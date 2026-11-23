import { z } from "zod";
import { notifier } from "../notifier/contract.ts";
import { add, build, checkBuild, noteFromA, noteFromB, ping, run } from "./commands.ts";
import { automation, machine } from "./data.ts";
import { built, checked, failed, noted, pinged } from "./events.ts";

// One automation: run emits failed again.
export const retry = automation({
  receives: { failed },
  commands: { run },
}).send({});

// Two automations: the cycle is reported once, at the automation defined first.
export const check = automation({
  receives: { built },
  commands: { checkBuild },
}).send({});
export const rebuild = automation({
  receives: { checked },
  commands: { build },
}).send({});

// Two cycles through notify: each is reported once.
export const notify = automation({ receives: { noted }, commands: { ping } }).send({});
export const noteA = automation({
  receives: { pinged },
  commands: { noteFromA },
}).send({});
export const noteB = automation({
  receives: { pinged },
  commands: { noteFromB },
}).send({});

// A cycle through a machine is not reported, because a machine waits and its guard can stop the cycle.
export const noter = machine({
  description: "Write note A on the first three pings",
  context: { count: z.int().default(0) },
  receives: { pinged },
  commands: { noteFromA },
  initial: "idle",
  states: { idle: {}, noting: {} },
}).chart({
  states: {
    idle: { on: { pinged: [{ guard: { belowThree: ({ context }) => context.count < 3 }, target: "noting" }] } },
    noting: {
      entry: { assign: { count: ({ context }) => context.count + 1 } },
      sends: { noteFromA: { onAccepted: [{ target: "idle" }] } },
    },
  },
});

// A cycle through another service is reported.
export const readd = automation({
  receives: { noticed: notifier.noticed },
  commands: { add },
}).send({});

// An automation that leads into another cycle is not itself on a cycle.
export const buildOnNotice = automation({
  receives: { noticed: notifier.noticed },
  commands: { build },
}).send({});
