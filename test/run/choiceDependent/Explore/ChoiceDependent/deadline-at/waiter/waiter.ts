import { bag, datetime, emit, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Once = singleEntity({ description: "Went", fields: { went: z.boolean().default(false) } });
export const { command, machine, event, updateEvent, contract, scenario } = service({
  name: "waiter",
  description: "Ping once a deadline whose time one event sets is due",
  entities: { Once },
});
export const went = updateEvent({ entity: Once, writes: ["went"] });

export const e1 = event({});
export const e2 = event({});
export const pinged = event({});
export const go = command({
  input: { ks: bag(z.string()) },
  emits: [went, e1, e2],
  requires: { first: ({ records }) => !records.Once.went },
}).decide(({ input }) => [emit(went, { went: true }), input.ks.map((k) => (k === "1" ? emit(e1, {}) : emit(e2, {})))]);
export const ping = command({ emits: [pinged] }).decide(() => [emit(pinged, {})]);

export const m = machine({
  description: "e1 enters waiting, whose at reads due; e2 moves due",
  context: { due: datetime.nullable().default(null) },
  receives: { e1, e2 },
  commands: { ping },
  initial: "idle",
  states: { idle: {}, waiting: {}, pinging: {}, done: {} },
}).chart({
  on: { e2: [{ assign: { due: () => Temporal.Instant.from("2026-10-25T06:00:00Z") } }] },
  states: {
    idle: { on: { e1: [{ target: "waiting" }] } },
    waiting: {
      after: {
        due: {
          at: ({ context }) => context.due ?? Temporal.Instant.from("2026-10-25T05:00:00Z"),
          onFired: [{ target: "pinging" }],
        },
      },
    },
    pinging: { sends: { ping: { input: () => ({}), onAccepted: [{ target: "done" }] } } },
  },
});

export const waiter = contract({ go, pinged });
