import { emit, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Board = singleEntity({
  description: "The board that counts its changes while loud",
  fields: { changes: z.int().min(0).default(0), mode: z.enum(["quiet", "loud"]).default("quiet") },
});

export const { command, updateEvent, bounds } = service({
  name: "board",
  description: "Toggle the board",
  entities: { Board },
  invariants: { fewChanges: ({ records }) => records.Board.changes <= 3 },
});

export const boardChanged = updateEvent({ entity: Board, writes: ["changes", "mode"] });

export const toggle = command({ callers: ["client"], emits: [boardChanged] }).decide(({ records }) =>
  records.Board.mode === "quiet" ? [emit(boardChanged, { changes: records.Board.changes, mode: "loud" })] : [],
);

export const quiet = command({ callers: ["client"], emits: [boardChanged] }).decide(({ records }) => [
  ...(records.Board.changes < 3 ? [emit(boardChanged, { changes: records.Board.changes + 1, mode: "quiet" })] : []),
]);

export const boardBounds = bounds({ creates: {} });
