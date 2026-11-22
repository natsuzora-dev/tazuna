import { emit, parseInstant, service } from "@natsuzora-dev/tazuna";
import { pager } from "../pager/contract.ts";

export const { command, machine, event, contract, scenario } = service({
  name: "pagers",
  description: "Page at 10:00 from two clocks",
});

export const armed = event({});

export const arm = command({ emits: [armed] }).decide(() => [emit(armed, {})]);

const pagerClock = (by: string) =>
  machine({
    description: `Page as ${by} at 10:00 once armed`,
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
      paging: { sends: { page: { input: () => ({ by }), onAccepted: [{ target: "done" }] } } },
    },
  });

export const first = pagerClock("first");
export const second = pagerClock("second");

export const pagers = contract({ arm });
