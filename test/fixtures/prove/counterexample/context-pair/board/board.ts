import { emit, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Board = singleEntity({
  description: "The board",
  fields: { a: z.boolean().default(false), b: z.boolean().default(false) },
});

export const { command, automation, machine, event, updateEvent } = service({
  name: "board",
  description: "Show the reply that each ping causes, and report later what b saw",
  entities: { Board },
});

export const pinged = event({ payload: { at: z.int() } });
export const aShown = updateEvent({ entity: Board, writes: ["a"] });
export const bShown = updateEvent({ entity: Board, writes: ["b"] });
export const reported = event({ payload: { sawA: z.boolean() } });

export const ping = command({ callers: ["client"], input: { at: z.int() }, emits: [pinged] }).decide(({ input }) => [
  emit(pinged, { at: input.at }),
]);

export const showA = command({ callers: ["board"], input: { shown: z.boolean() }, emits: [aShown] }).decide(
  ({ input }) => [emit(aShown, { a: input.shown })],
);

export const showB = command({ callers: ["board"], input: { shown: z.boolean() }, emits: [bShown] }).decide(
  ({ input }) => [emit(bShown, { b: input.shown })],
);

export const report = command({ callers: ["board"], input: { sawA: z.boolean() }, emits: [reported] }).decide(
  ({ input }) => [emit(reported, { sawA: input.sawA })],
);

export const replyA = automation({ receives: { pinged }, commands: { showA } }).send({
  input: () => ({ shown: true }),
});

export const replyB = automation({ receives: { pinged }, commands: { showB } }).send({
  input: () => ({ shown: true }),
});

// Both orders of showA and showB end with the same records and out lines and the watcher seen, and its context holds
// a as it was before or after showA, which the report a minute later writes out.
export const watcher = machine({
  description: "Note a when b is shown, and report it a minute later",
  context: { sawA: z.boolean().default(false) },
  receives: { bShown },
  commands: { report },
  initial: "idle",
  states: { idle: {}, seen: {}, reporting: {} },
}).chart({
  states: {
    idle: { on: { bShown: [{ target: "seen", assign: { sawA: ({ records }) => records.Board.a } }] } },
    seen: { after: { minute: { delay: 60_000, onFired: [{ target: "reporting" }] } } },
    reporting: {
      sends: {
        report: {
          input: ({ context }) => ({ sawA: context.sawA }),
          onAccepted: [{ target: "idle" }],
        },
      },
    },
  },
});
