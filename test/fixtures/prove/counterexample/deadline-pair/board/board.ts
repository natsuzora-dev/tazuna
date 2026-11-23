import { emit, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Board = singleEntity({
  description: "The board",
  fields: { a: z.boolean().default(false), b: z.boolean().default(false) },
});

export const { command, automation, machine, event, updateEvent } = service({
  name: "board",
  description: "Show the reply that each ping causes, and ring an hour after a showing",
  entities: { Board },
});

export const pinged = event({ payload: { at: z.int() } });
export const aShown = updateEvent({ entity: Board, writes: ["a"] });
export const bShown = updateEvent({ entity: Board, writes: ["b"] });
export const rang = event({});

export const ping = command({ callers: ["client"], input: { at: z.int() }, emits: [pinged] }).decide(({ input }) => [
  emit(pinged, { at: input.at }),
]);

export const showA = command({ callers: ["board"], input: { shown: z.boolean() }, emits: [aShown] }).decide(
  ({ input }) => [emit(aShown, { a: input.shown })],
);

export const showB = command({ callers: ["board"], input: { shown: z.boolean() }, emits: [bShown] }).decide(
  ({ input }) => [emit(bShown, { b: input.shown })],
);

export const ring = command({ callers: ["board"], emits: [rang] }).decide(() => [emit(rang, {})]);

export const replyA = automation({ receives: { pinged }, commands: { showA } }).send({
  input: () => ({ shown: true }),
});

export const replyB = automation({ receives: { pinged }, commands: { showB } }).send({
  input: () => ({ shown: true }),
});

// Both orders of showA and showB end with the same records and out lines and the bell waiting, and its hour starts
// again only when b is shown after a, so the bell rings at another time.
export const bell = machine({
  description: "Ring an hour after the board shows b after a",
  receives: { bShown },
  commands: { ring },
  initial: "waiting",
  states: { waiting: {}, ringing: {} },
}).chart({
  states: {
    waiting: {
      on: { bShown: [{ guard: { afterA: ({ records }) => records.Board.a }, target: "waiting", reenter: true }] },
      after: { hour: { delay: 3_600_000, onFired: [{ target: "ringing" }] } },
    },
    ringing: { sends: { ring: { onAccepted: [{ target: "waiting" }] } } },
  },
});
