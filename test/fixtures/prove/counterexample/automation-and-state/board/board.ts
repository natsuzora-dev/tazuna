import { emit, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Board = singleEntity({
  description: "The board",
  fields: { a: z.boolean().default(false), b: z.boolean().default(false) },
});

export const { command, automation, machine, event, updateEvent } = service({
  name: "board",
  description: "Show the reply that each ping causes",
  entities: { Board },
});

export const pinged = event({ payload: { at: z.int() } });
export const aShown = updateEvent({ entity: Board, writes: ["a"] });
export const bShown = updateEvent({ entity: Board, writes: ["b"] });

export const ping = command({ callers: ["client"], input: { at: z.int() }, emits: [pinged] }).decide(({ input }) => [
  emit(pinged, { at: input.at }),
]);

export const showA = command({ callers: ["board"], input: { shown: z.boolean() }, emits: [aShown] }).decide(
  ({ input }) => [emit(aShown, { a: input.shown })],
);

// One ping makes replyA send showA and copier send copyA, which no line orders: b takes a before or after showA.
export const copyA = command({ callers: ["board"], input: { shown: z.boolean() }, emits: [bShown] }).decide(
  ({ records }) => [emit(bShown, { b: records.Board.a })],
);

export const replyA = automation({ receives: { pinged }, commands: { showA } }).send({
  input: () => ({ shown: true }),
});

export const copier = machine({
  description: "Copy a into b on each ping",
  receives: { pinged },
  commands: { copyA },
  initial: "idle",
  states: { idle: {}, copying: {} },
}).chart({
  on: { pinged: [{ target: "copying" }] },
  states: {
    copying: {
      sends: {
        copyA: { input: () => ({ shown: true }), onAccepted: [{ target: "idle" }], onRejected: [{ target: "idle" }] },
      },
    },
  },
});
