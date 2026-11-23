import { emit, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Counter = singleEntity({
  description: "How many bumps the counter took",
  fields: { count: z.int().default(0) },
});

export const { automation, command, event, updateEvent, contract, scenario } = service({
  name: "counter",
  description: "Bump one counter from five automations",
  entities: { Counter },
});

export const ticked = event({});
export const counted = updateEvent({ entity: Counter, writes: ["count"] });

export const tick = command({ emits: [ticked] }).decide(() => [emit(ticked, {})]);

const bump = () =>
  command({ emits: [counted] }).decide(({ records }) => [emit(counted, { count: records.Counter.count + 1 })]);

export const bumpA = bump();
export const bumpB = bump();
export const bumpC = bump();
export const bumpD = bump();
export const bumpE = bump();

export const bumpWithA = automation({ receives: { ticked }, commands: { bumpA } }).send({});
export const bumpWithB = automation({ receives: { ticked }, commands: { bumpB } }).send({});
export const bumpWithC = automation({ receives: { ticked }, commands: { bumpC } }).send({});
export const bumpWithD = automation({ receives: { ticked }, commands: { bumpD } }).send({});
export const bumpWithE = automation({ receives: { ticked }, commands: { bumpE } }).send({});

export const counter = contract({ tick });
