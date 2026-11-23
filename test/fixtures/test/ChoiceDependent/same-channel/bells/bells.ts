import { emit, parseInstant, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { pager } from "../pager/contract.ts";

export const { command, machine, event, contract, scenario } = service({
  name: "bells",
  description: "Ring a bell at 10:00 from two clocks",
});

export const armed = event({});
export const rang = event({ payload: { by: z.string() } });

export const arm = command({ callers: ["client"], emits: [armed] }).decide(() => [emit(armed, {})]);

export const ring = command({ callers: ["client", "bells"], input: { by: z.string() }, emits: [rang] }).decide(
  ({ input }) => [emit(rang, { by: input.by })],
);

export const first = machine({
  description: `Ring as first at 10:00 once armed: emit rang and page`,
  receives: { armed },
  commands: { ring, page: pager.page },
  initial: "idle",
  states: { idle: {}, waiting: {}, ringing: {}, paging: {}, done: { type: "final" } },
}).chart({
  states: {
    idle: { on: { armed: [{ target: "waiting" }] } },
    waiting: {
      after: { due: { at: () => parseInstant("2026-10-25T01:00:00Z"), onFired: [{ target: "ringing" }] } },
    },
    ringing: {
      sends: { ring: { input: () => ({ by: "first" }), onAccepted: [{ target: "paging" }] } },
    },
    paging: {
      sends: { page: { input: () => ({ by: "first" }), onAccepted: [{ target: "done" }] } },
    },
  },
});

export const second = machine({
  description: `Ring as second at 10:00 once armed: emit rang and page`,
  receives: { armed },
  commands: { ring, page: pager.page },
  initial: "idle",
  states: { idle: {}, waiting: {}, ringing: {}, paging: {}, done: { type: "final" } },
}).chart({
  states: {
    idle: { on: { armed: [{ target: "waiting" }] } },
    waiting: {
      after: { due: { at: () => parseInstant("2026-10-25T01:00:00Z"), onFired: [{ target: "ringing" }] } },
    },
    ringing: {
      sends: { ring: { input: () => ({ by: "second" }), onAccepted: [{ target: "paging" }] } },
    },
    paging: {
      sends: { page: { input: () => ({ by: "second" }), onAccepted: [{ target: "done" }] } },
    },
  },
});

export const bells = contract({ arm, rang });
