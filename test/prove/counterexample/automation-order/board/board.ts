import { emit, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Board = singleEntity({
  description: "The board that shows the last reply",
  fields: { last: z.enum(["none", "a", "b"]).default("none") },
});

export const { command, automation, event, updateEvent } = service({
  name: "board",
  description: "Show the reply that each ping causes",
  entities: { Board },
});

export const pinged = event({ payload: { at: z.int() } });
export const lastChanged = updateEvent({ entity: Board, writes: ["last"] });

export const ping = command({ input: { at: z.int() }, emits: [pinged] }).decide(({ input }) => [
  emit(pinged, { at: input.at }),
]);

export const show = command({ input: { last: z.enum(["a", "b"]) }, emits: [lastChanged] }).decide(({ input }) => [
  emit(lastChanged, { last: input.last }),
]);

export const replyA = automation({ receives: { pinged }, commands: { show } }).send({ input: () => ({ last: "a" }) });

export const replyB = automation({ receives: { pinged }, commands: { show } }).send({ input: () => ({ last: "b" }) });
