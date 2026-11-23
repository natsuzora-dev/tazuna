import { emit, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Board = singleEntity({
  description: "The board that shows which replies came",
  fields: { a: z.boolean().default(false), b: z.boolean().default(false) },
});

export const { command, automation, event, updateEvent } = service({
  name: "board",
  description: "Show the reply that each ping causes",
  entities: { Board },
});

export const pinged = event({ payload: { at: z.int() } });
export const aShown = updateEvent({ entity: Board, writes: ["a"] });
export const aSaw = event({ payload: { b: z.boolean() } });
export const bShown = updateEvent({ entity: Board, writes: ["b"] });

export const ping = command({ callers: ["client"], input: { at: z.int() }, emits: [pinged] }).decide(({ input }) => [
  emit(pinged, { at: input.at }),
]);

// The records end the same in both orders of showA and showB, and aSaw carries b as it was before or after showB.
export const showA = command({
  callers: ["client", "board"],
  input: { shown: z.boolean() },
  emits: [aShown, aSaw],
}).decide(({ input, records }) => [emit(aShown, { a: input.shown }), emit(aSaw, { b: records.Board.b })]);

export const showB = command({ callers: ["client", "board"], input: { shown: z.boolean() }, emits: [bShown] }).decide(
  ({ input }) => [emit(bShown, { b: input.shown })],
);

export const replyA = automation({ receives: { pinged }, commands: { showA } }).send({
  input: () => ({ shown: true }),
});

export const replyB = automation({ receives: { pinged }, commands: { showB } }).send({
  input: () => ({ shown: true }),
});
