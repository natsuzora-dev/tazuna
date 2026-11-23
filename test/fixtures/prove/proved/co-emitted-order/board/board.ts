import { emit, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Board = singleEntity({
  description: "The board that marks each reply",
  fields: { a: z.boolean().default(false), b: z.boolean().default(false) },
});

export const { command, automation, event, updateEvent } = service({
  name: "board",
  description: "Show the reply to each of the two events that one ping emits",
  entities: { Board },
});

export const pingedA = event({});
export const pingedB = event({});
export const aMarked = updateEvent({ entity: Board, writes: ["a"] });
export const bMarked = updateEvent({ entity: Board, writes: ["b"] });

export const ping = command({ callers: ["client"], emits: [pingedA, pingedB] }).decide(() => [
  emit(pingedA, {}),
  emit(pingedB, {}),
]);

export const markA = command({ callers: ["board"], emits: [aMarked] }).decide(() => [emit(aMarked, { a: true })]);

export const markB = command({ callers: ["board"], emits: [bMarked] }).decide(() => [emit(bMarked, { b: true })]);

export const replyA = automation({ receives: { pingedA }, commands: { markA } }).send({});

export const replyB = automation({ receives: { pingedB }, commands: { markB } }).send({});
