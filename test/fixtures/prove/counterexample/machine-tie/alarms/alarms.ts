import { emit, parseInstant, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Flag = singleEntity({
  description: "Whether the first clock rang",
  fields: { set: z.boolean().default(false) },
});

export const { command, machine, updateEvent } = service({
  name: "alarms",
  description: "Ring an alarm at 10:00 from two clocks",
  entities: { Flag },
});

export const flagSet = updateEvent({ entity: Flag, writes: ["set"] });

export const setFlag = command({ callers: ["alarms"], emits: [flagSet] }).decide(() => [emit(flagSet, { set: true })]);

export const first = machine({
  description: "Ring as first",
  commands: { setFlag },
  initial: "waiting",
  states: { waiting: {}, ringing: {}, done: {} },
}).chart({
  states: {
    waiting: {
      after: { due: { at: () => parseInstant("2026-10-25T01:00:00Z"), onFired: [{ target: "ringing" }] } },
    },
    ringing: {
      sends: { setFlag: { input: () => ({}), onAccepted: [{ target: "done" }], onRejected: [{ target: "done" }] } },
    },
  },
});

// The records end the same in both orders of the two deadlines, and this machine ends late or early.
export const second = machine({
  description: "Note whether the first clock rang before",
  initial: "waiting",
  states: { waiting: {}, late: {}, early: {} },
}).chart({
  states: {
    waiting: {
      after: {
        due: {
          at: () => parseInstant("2026-10-25T01:00:00Z"),
          onFired: [{ guard: { flagged: ({ records }) => records.Flag.set }, target: "late" }, { target: "early" }],
        },
      },
    },
  },
});
