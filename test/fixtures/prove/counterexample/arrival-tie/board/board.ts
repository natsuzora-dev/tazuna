import { emit, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { sensor } from "../sensor/contract.ts";

export const Door = singleEntity({
  description: "The door as the last reading tells",
  fields: { state: z.enum(["unknown", "open", "closed"]).default("unknown") },
});

export const { command, automation, updateEvent } = service({
  name: "board",
  description: "Show the door as the sensor reports it",
  entities: { Door },
});

export const doorChanged = updateEvent({ entity: Door, writes: ["state"] });

export const show = command({
  callers: ["board"],
  input: { state: z.enum(["open", "closed"]) },
  emits: [doorChanged],
}).decide(({ input }) => [emit(doorChanged, { state: input.state })]);

export const showReading = automation({ receives: { read: sensor.read }, commands: { show } }).send({
  input: ({ payload }) => ({ state: payload.state }),
});
