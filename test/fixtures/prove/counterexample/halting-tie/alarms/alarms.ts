import { addDays, date, emit, entity, parseInstant, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Alarm = singleEntity({
  description: "Which clocks rang the alarm",
  fields: { first: z.boolean().default(false) },
});

export const Note = entity({
  description: "A note",
  fields: { id: z.string(), due: date },
  key: "id",
});

export const { command, machine, updateEvent, createEvent, bounds } = service({
  name: "alarms",
  description: "Ring an alarm at 10:00 from two clocks",
  entities: { Alarm, Note },
});

export const firstRang = updateEvent({ entity: Alarm, writes: ["first"] });
export const noted = createEvent({ entity: Note });

export const ringFirst = command({ callers: ["alarms"], input: { by: z.boolean() }, emits: [firstRang] }).decide(() => [
  emit(firstRang, { first: true }),
]);

// addDays past the last date throws, so ringSecond halts only after ringFirst, in one order of the two deadlines.
export const ringSecond = command({ callers: ["alarms"], input: { by: z.boolean() }, emits: [noted] }).decide(
  ({ records }) => {
    const n = records.Note.get("x");
    return records.Alarm.first && n !== undefined && addDays(n.due, 3_000_000) > n.due ? [] : [];
  },
);

export const alarmsBounds = bounds({ creates: { Note: 1 } });

export const first = machine({
  description: "Ring as first",
  commands: { ringFirst },
  initial: "waiting",
  states: { waiting: {}, ringing: {}, done: {} },
}).chart({
  states: {
    waiting: {
      after: { due: { at: () => parseInstant("2026-10-25T01:00:00Z"), onFired: [{ target: "ringing" }] } },
    },
    ringing: {
      sends: {
        ringFirst: { input: () => ({ by: true }), onAccepted: [{ target: "done" }], onRejected: [{ target: "done" }] },
      },
    },
  },
});

export const second = machine({
  description: "Ring as second",
  commands: { ringSecond },
  initial: "waiting",
  states: { waiting: {}, ringing: {}, done: {} },
}).chart({
  states: {
    waiting: {
      after: { due: { at: () => parseInstant("2026-10-25T01:00:00Z"), onFired: [{ target: "ringing" }] } },
    },
    ringing: {
      sends: {
        ringSecond: { input: () => ({ by: true }), onAccepted: [{ target: "done" }], onRejected: [{ target: "done" }] },
      },
    },
  },
});
