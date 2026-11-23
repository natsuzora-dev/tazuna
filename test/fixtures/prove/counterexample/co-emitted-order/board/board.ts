import { emit, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Board = singleEntity({
  description: "The board that shows the last reply",
  fields: { last: z.enum(["none", "a", "b"]).default("none") },
});

export const { command, automation, event, updateEvent } = service({
  name: "board",
  description: "Show the reply to each of the two events that one ping emits",
  entities: { Board },
});

export const pingedA = event({});
export const pingedB = event({});
export const lastChanged = updateEvent({ entity: Board, writes: ["last"] });

export const ping = command({ callers: ["client"], emits: [pingedA, pingedB] }).decide(() => [
  emit(pingedA, {}),
  emit(pingedB, {}),
]);

export const show = command({
  callers: ["board"],
  input: { last: z.enum(["a", "b"]) },
  emits: [lastChanged],
}).decide(({ input }) => [emit(lastChanged, { last: input.last })]);

export const replyA = automation({ receives: { pingedA }, commands: { show } }).send({ input: () => ({ last: "a" }) });

export const replyB = automation({ receives: { pingedB }, commands: { show } }).send({ input: () => ({ last: "b" }) });
