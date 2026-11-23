import { bag, emit, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Door = singleEntity({ description: "Used", fields: { used: z.boolean().default(false) } });
export const { command, machine, event, updateEvent, contract, scenario, condition } = service({
  name: "door",
  description: "Open and close a door, and remember who touched it last, from unordered events",
  entities: { Door },
});
export const used = updateEvent({ entity: Door, writes: ["used"] });

const first = condition(({ records }) => !records.Door.used);

export const opened = event({});
export const closed = event({});
export const touched = event({ payload: { by: z.string() } });

export const go = command({
  callers: ["client"],
  input: { ks: bag(z.string()) },
  emits: [used, opened, closed],
  requires: { first },
}).decide(({ input }) => [
  emit(used, { used: true }),
  input.ks.map((k) => (k === "open" ? emit(opened, {}) : emit(closed, {}))),
]);
export const touch = command({
  callers: ["client"],
  input: { by: bag(z.string()) },
  emits: [used, touched],
  requires: { first },
}).decide(({ input }) => [emit(used, { used: true }), input.by.map((by) => emit(touched, { by }))]);

export const door = machine({
  description: "opened enters open and closed enters shut; touched keeps who touched last in the context",
  context: { last: z.string().default("") },
  receives: { opened, closed, touched },
  initial: "shut",
  states: { shut: {}, open: {} },
}).chart({
  on: {
    opened: [{ target: "open" }],
    closed: [{ target: "shut" }],
    touched: [{ assign: { last: ({ payload }) => payload.by } }],
  },
});

export const doors = contract({ go, touch });
