import { emit, service } from "@natsuzora-dev/tazuna";
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

const pinger = (by: string, due: string) =>
  machine({
    description: `Ping as ${by} once armed, and pong at ${due}`,
    receives: { armed },
    commands: { ping, pong },
    initial: "idle",
    states: { idle: {}, pinging: {}, waiting: {}, ponging: {}, done: { type: "final" } },
  }).chart({
    states: {
      idle: { on: { armed: [{ target: "pinging" }] } },
      pinging: { sends: { ping: { input: () => ({ by }), onAccepted: [{ target: "waiting" }] } } },
      waiting: { after: { due: { at: () => Temporal.Instant.from(due), onFired: [{ target: "ponging" }] } } },
      ponging: { sends: { pong: { input: () => ({ by }), onAccepted: [{ target: "done" }] } } },
    },
  });

export const late = pinger("late", "2026-10-25T01:00:00Z");
export const overdue = pinger("overdue", "2026-10-24T00:00:00Z");

export const sender = contract({ arm, pinged, ponged });
