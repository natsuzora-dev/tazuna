import { emit, parseInstant, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Alarm = singleEntity({ description: "Who rang the alarm last", fields: { by: z.string().default("") } });

export const { command, machine, event, updateEvent } = service({
  name: "alarms",
  description: "Ring an alarm at 10:00 from two clocks",
  entities: { Alarm },
});

export const rang = updateEvent({ entity: Alarm, writes: ["by"] });

export const ring = command({ callers: ["alarms"], input: { by: z.string() }, emits: [rang] }).decide(({ input }) => [
  emit(rang, { by: input.by }),
]);

export const first = machine({
  description: "Ring the alarm as first at 10:00",
  commands: { ring },
  initial: "waiting",
  states: { waiting: {}, ringing: {}, done: {} },
}).chart({
  states: {
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
  description: "Ring the alarm as second at 10:00",
  commands: { ring },
  initial: "waiting",
  states: { waiting: {}, ringing: {}, done: {} },
}).chart({
  states: {
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
