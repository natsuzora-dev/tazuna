import { bag, emit, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Latch = singleEntity({ description: "Used", fields: { used: z.boolean().default(false) } });
export const { command, machine, event, updateEvent, contract, scenario } = service({
  name: "latch",
  description: "Leave work, and resume it where it was left",
  entities: { Latch },
});
export const used = updateEvent({ entity: Latch, writes: ["used"] });
export const next = event({});
export const stop = event({});
export const resume = event({});

export const go = command({
  callers: ["client"],
  input: { ks: bag(z.string()) },
  emits: [used, next, stop, resume],
}).decide(({ input }) => [
  emit(used, { used: true }),
  input.ks.map((k) => (k === "next" ? emit(next, {}) : k === "stop" ? emit(stop, {}) : emit(resume, {}))),
]);

export const latch = machine({
  description: "working.a -next-> working.b; stop leaves working for idle; resume returns to the child it left",
  receives: { next, stop, resume },
  initial: "working",
  states: { idle: {}, working: { initial: "a", states: { a: {}, b: {}, back: { type: "history" } } } },
}).chart({
  states: {
    idle: { on: { resume: [{ target: "back" }] } },
    a: { on: { next: [{ target: "b" }] } },
    working: { on: { stop: [{ target: "idle" }] } },
  },
});

export const latches = contract({ go });
