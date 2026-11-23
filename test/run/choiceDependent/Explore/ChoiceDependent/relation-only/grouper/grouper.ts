import { emit, entity, parseInstant, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Mark = singleEntity({ description: "Whether mark ran", fields: { set: z.boolean().default(false) } });

export const Item = entity({ description: "A number to emit", fields: { id: z.string(), n: z.int() }, key: "id" });

export const { command, machine, event, updateEvent, contract, scenario } = service({
  name: "grouper",
  description: "Emit two events in one group once marked, or in two groups before",
  entities: { Mark, Item },
});

export const armed = event({});
export const marked = updateEvent({ entity: Mark, writes: ["set"] });
export const paired = event({ payload: { n: z.int() } });

export const arm = command({ callers: ["client"], emits: [armed] }).decide(() => [emit(armed, {})]);

export const mark = command({ callers: ["client", "grouper"], emits: [marked] }).decide(() => [
  emit(marked, { set: true }),
]);

export const pair = command({ callers: ["client", "grouper"], emits: [paired] }).decide(({ records }) =>
  records.Mark.set
    ? [records.Item.map((item) => emit(paired, { n: item.n }))]
    : [emit(paired, { n: 1 }), emit(paired, { n: 2 })],
);

const waiting = {
  after: {
    due: { at: () => parseInstant("2026-10-25T01:00:00Z"), onFired: [{ target: "sending" as const }] },
  },
};

export const marker = machine({
  description: "Send mark at 10:00 once armed",
  receives: { armed },
  commands: { mark },
  initial: "idle",
  states: { idle: {}, waiting: {}, sending: {}, done: { type: "final" } },
}).chart({
  states: {
    idle: { on: { armed: [{ target: "waiting" }] } },
    waiting,
    sending: {
      sends: { mark: { input: () => ({}), onAccepted: [{ target: "done" }], onRejected: [{ target: "done" }] } },
    },
  },
});

export const pairer = machine({
  description: "Send pair at 10:00 once armed",
  receives: { armed },
  commands: { pair },
  initial: "idle",
  states: { idle: {}, waiting: {}, sending: {}, done: { type: "final" } },
}).chart({
  states: {
    idle: { on: { armed: [{ target: "waiting" }] } },
    waiting,
    sending: { sends: { pair: { input: () => ({}), onAccepted: [{ target: "done" }] } } },
  },
});

export const grouper = contract({ arm, paired });
