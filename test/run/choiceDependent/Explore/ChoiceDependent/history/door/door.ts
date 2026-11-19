import { bag, emit, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Door = singleEntity({ description: "Used", fields: { used: z.boolean().default(false) } });
export const { command, machine, event, updateEvent, contract, scenario } = service({
  name: "door",
  description: "Leave work from unordered events; no state reads where it was left",
  entities: { Door },
});
export const used = updateEvent({ entity: Door, writes: ["used"] });
export const next = event({});
export const stop = event({});

export const go = command({
  input: { ks: bag(z.string()) },
  emits: [used, next, stop],
}).decide(({ input }) => [
  emit(used, { used: true }),
  input.ks.map((k) => (k === "next" ? emit(next, {}) : emit(stop, {}))),
]);

export const door = machine({
  description: "working.a -next-> working.b; stop leaves working for idle; no history state",
  receives: { next, stop },
  initial: "working",
  states: { idle: {}, working: { initial: "a", states: { a: {}, b: {} } } },
}).chart({
  states: {
    a: { on: { next: [{ target: "b" }] } },
    working: { on: { stop: [{ target: "idle" }] } },
  },
});

export const doors = contract({ go });
