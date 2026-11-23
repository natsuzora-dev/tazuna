import { emit, parseInstant, service } from "@natsuzora-dev/tazuna";
import { pager } from "../pager/contract.ts";

export const { command, machine, event, contract, scenario } = service({
  name: "pagers",
  description: "Page at 10:00 from two clocks",
});

export const armed = event({});

export const arm = command({ callers: ["client"], emits: [armed] }).decide(() => [emit(armed, {})]);

export const first = machine({
  description: `Page as first at 10:00 once armed`,
  receives: { armed },
  commands: { page: pager.page },
  initial: "idle",
  states: { idle: {}, waiting: {}, paging: {}, done: { type: "final" } },
}).chart({
  states: {
    idle: { on: { armed: [{ target: "waiting" }] } },
    waiting: {
      after: { due: { at: () => parseInstant("2026-10-25T01:00:00Z"), onFired: [{ target: "paging" }] } },
    },
    paging: { sends: { page: { input: () => ({ by: "first" }), onAccepted: [{ target: "done" }] } } },
  },
});

export const second = machine({
  description: `Page as second at 10:00 once armed`,
  receives: { armed },
  commands: { page: pager.page },
  initial: "idle",
  states: { idle: {}, waiting: {}, paging: {}, done: { type: "final" } },
}).chart({
  states: {
    idle: { on: { armed: [{ target: "waiting" }] } },
    waiting: {
      after: { due: { at: () => parseInstant("2026-10-25T01:00:00Z"), onFired: [{ target: "paging" }] } },
    },
    paging: { sends: { page: { input: () => ({ by: "second" }), onAccepted: [{ target: "done" }] } } },
  },
});

export const pagers = contract({ arm });
