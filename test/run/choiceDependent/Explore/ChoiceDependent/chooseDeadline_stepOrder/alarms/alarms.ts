import { emit, parseInstant, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Alarm = singleEntity({ description: "Who rang the alarm last", fields: { by: z.string().default("") } });

export const { command, machine, event, updateEvent, contract, scenario } = service({
  name: "alarms",
  description: "Ring an alarm at 10:00 from two clocks",
  entities: { Alarm },
});

export const armed = event({});
export const rang = updateEvent({ entity: Alarm, writes: ["by"] });

export const arm = command({ emits: [armed] }).decide(() => [emit(armed, {})]);

export const ring = command({ input: { by: z.string() }, emits: [rang] }).decide(({ input }) => [
  emit(rang, { by: input.by }),
]);

export const first = machine({
  description: `Ring the alarm as first at 10:00 once armed`,
  receives: { armed },
  commands: { ring },
  initial: "idle",
  states: { idle: {}, waiting: {}, ringing: {}, done: { type: "final" } },
}).chart({
  states: {
    idle: { on: { armed: [{ target: "waiting" }] } },
    waiting: {
      after: { due: { at: () => parseInstant("2026-10-25T01:00:00Z"), onFired: [{ target: "ringing" }] } },
    },
    ringing: {
      sends: {
        ring: { input: () => ({ by: "first" }), onAccepted: [{ target: "done" }], onRejected: [{ target: "done" }] },
      },
    },
  },
});

export const second = machine({
  description: `Ring the alarm as second at 10:00 once armed`,
  receives: { armed },
  commands: { ring },
  initial: "idle",
  states: { idle: {}, waiting: {}, ringing: {}, done: { type: "final" } },
}).chart({
  states: {
    idle: { on: { armed: [{ target: "waiting" }] } },
    waiting: {
      after: { due: { at: () => parseInstant("2026-10-25T01:00:00Z"), onFired: [{ target: "ringing" }] } },
    },
    ringing: {
      sends: {
        ring: { input: () => ({ by: "second" }), onAccepted: [{ target: "done" }], onRejected: [{ target: "done" }] },
      },
    },
  },
});

export const alarms = contract({ arm });
