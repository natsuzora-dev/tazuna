import { emit, parseInstant, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, machine, event, contract, given, scenario } = service({
  name: "sender",
  description: "Ping on arming and pong at each machine's deadline",
});

export const armed = event({});
export const pinged = event({ payload: { by: z.string() } });
export const ponged = event({ payload: { by: z.string() } });

export const arm = command({ emits: [armed] }).decide(() => [emit(armed, {})]);

export const ping = command({ input: { by: z.string() }, emits: [pinged] }).decide(({ input }) => [
  emit(pinged, { by: input.by }),
]);

export const pong = command({ input: { by: z.string() }, emits: [ponged] }).decide(({ input }) => [
  emit(ponged, { by: input.by }),
]);

export const late = machine({
  description: "Ping as late once armed, and pong at 2026-10-25T01:00:00Z",
  receives: { armed },
  commands: { ping, pong },
  initial: "idle",
  states: { idle: {}, pinging: {}, waiting: {}, ponging: {}, done: { type: "final" } },
}).chart({
  states: {
    idle: { on: { armed: [{ target: "pinging" }] } },
    pinging: { sends: { ping: { input: () => ({ by: "late" }), onAccepted: [{ target: "waiting" }] } } },
    waiting: { after: { due: { at: () => parseInstant("2026-10-25T01:00:00Z"), onFired: [{ target: "ponging" }] } } },
    ponging: { sends: { pong: { input: () => ({ by: "late" }), onAccepted: [{ target: "done" }] } } },
  },
});

export const overdue = machine({
  description: "Ping as overdue once armed, and pong at 2026-10-24T00:00:00Z",
  receives: { armed },
  commands: { ping, pong },
  initial: "idle",
  states: { idle: {}, pinging: {}, waiting: {}, ponging: {}, done: { type: "final" } },
}).chart({
  states: {
    idle: { on: { armed: [{ target: "pinging" }] } },
    pinging: { sends: { ping: { input: () => ({ by: "overdue" }), onAccepted: [{ target: "waiting" }] } } },
    waiting: { after: { due: { at: () => parseInstant("2026-10-24T00:00:00Z"), onFired: [{ target: "ponging" }] } } },
    ponging: { sends: { pong: { input: () => ({ by: "overdue" }), onAccepted: [{ target: "done" }] } } },
  },
});

export const sender = contract({ arm, pinged, ponged });
