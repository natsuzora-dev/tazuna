import { emit, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Board = singleEntity({
  description: "The board that counts the pings it answered",
  fields: { answered: z.int().min(0).default(0), mode: z.enum(["quiet", "loud"]).default("quiet") },
});

export const { command, automation, event, updateEvent, contract } = service({
  name: "board",
  description: "Answer pings while loud",
  entities: { Board },
});

export const pinged = event({ payload: { at: z.int() } });
export const boardChanged = updateEvent({ entity: Board, writes: ["answered", "mode"] });

export const ping = command({ callers: ["client"], input: { at: z.int() }, emits: [pinged] }).decide(({ input }) => [
  emit(pinged, { at: input.at }),
]);

// Only the automation sends answer, so it lists board alone as its caller.
export const answer = command({ callers: ["board"], emits: [boardChanged] }).decide(({ records }) => [
  emit(boardChanged, { answered: records.Board.answered + 1, mode: records.Board.mode }),
]);

// A decide that chooses between arrays has no encoding.
export const toggle = command({ callers: ["client"], emits: [boardChanged] }).decide(({ records }) =>
  records.Board.mode === "quiet" ? [emit(boardChanged, { answered: records.Board.answered, mode: "loud" })] : [],
);

export const answerWhileLoud = automation({ receives: { pinged }, commands: { answer } }).send({
  guard: { loud: ({ records }) => records.Board.mode === "loud" },
});

export const board = contract({ ping, toggle });
