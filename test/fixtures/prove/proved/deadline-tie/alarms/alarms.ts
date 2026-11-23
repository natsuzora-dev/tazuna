import { emit, parseInstant, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Alarm = singleEntity({
  description: "Which clocks rang the alarm",
  fields: { first: z.boolean().default(false), second: z.boolean().default(false) },
});

export const { command, machine, event, updateEvent } = service({
  name: "alarms",
  description: "Ring an alarm at 10:00 from two clocks, each marking its own field",
  entities: { Alarm },
});

export const firstRang = updateEvent({ entity: Alarm, writes: ["first"] });
export const secondRang = updateEvent({ entity: Alarm, writes: ["second"] });

export const ring = command({
  callers: ["alarms"],
  input: { by: z.enum(["first", "second"]) },
  emits: [firstRang, secondRang],
}).decide(({ input }) =>
  input.by === "first" ? [emit(firstRang, { first: true })] : [emit(secondRang, { second: true })],
);

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
