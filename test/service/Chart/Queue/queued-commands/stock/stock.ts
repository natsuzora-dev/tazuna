import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Item = entity({ description: "An item in stock", fields: { id: z.string() }, key: "id" });

export const { command, machine, event, createEvent, contract, scenario } = service({
  name: "stock",
  description: "Keep the stock",
  entities: { Item },
});

export const started = event({});
export const prepared = createEvent({ entity: Item });
export const counted = event({});

export const start = command({ emits: [started] }).decide(() => [emit(started, {})]);

export const prepare = command({ emits: [prepared] }).decide(() => [emit(prepared, { id: "x" })]);

export const count = command({ emits: [counted] }).decide(() => [emit(counted, {})]);
