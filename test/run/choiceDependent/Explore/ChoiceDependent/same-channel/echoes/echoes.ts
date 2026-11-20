import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, machine, event, contract, scenario } = service({
  name: "echoes",
  description: "Echo the first bell that two clocks ring at 10:00",
});

export const armed = event({});
export const rang = event({ payload: { by: z.string() } });
export const echoed = event({});

export const arm = command({ emits: [armed] }).decide(() => [emit(armed, {})]);

export const ring = command({ input: { by: z.string() }, emits: [rang] }).decide(({ input }) => [
  emit(rang, { by: input.by }),
]);

export const echo = command({ emits: [echoed] }).decide(() => [emit(echoed, {})]);

const clock = (by: string) =>
  machine({
    description: `Ring as ${by} at 10:00 once armed`,
    receives: { armed },
    commands: { ring },
    initial: "idle",
    states: { idle: {}, waiting: {}, ringing: {}, done: { type: "final" } },
  }).chart({
    states: {
      idle: { on: { armed: [{ target: "waiting" }] } },
      waiting: {
        after: { due: { at: () => Temporal.Instant.from("2026-10-25T01:00:00Z"), onFired: [{ target: "ringing" }] } },
      },
      ringing: { sends: { ring: { input: () => ({ by }), onAccepted: [{ target: "done" }] } } },
    },
  });

export const first = clock("first");
export const second = clock("second");

export const hearer = machine({
  description: "Echo the first rang it hears, so echoed follows that one",
  receives: { rang },
  commands: { echo },
  initial: "listening",
  states: { listening: {}, echoing: {}, echoed: {} },
}).chart({
  states: {
    listening: { on: { rang: [{ target: "echoing" }] } },
    echoing: { on: { rang: [] }, sends: { echo: { input: () => ({}), onAccepted: [{ target: "echoed" }] } } },
    echoed: { on: { rang: [] } },
  },
});

export const echoes = contract({ arm, rang, echoed });
