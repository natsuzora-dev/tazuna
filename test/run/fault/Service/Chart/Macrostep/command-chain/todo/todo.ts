import { emit, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Counter = singleEntity({ description: "A counter", fields: { value: z.number().default(0) } });

export const { command, machine, updateEvent, scenario } = service({
  name: "todo",
  description: "Keep the tasks",
  entities: { Counter },
});

export const counted = updateEvent({ entity: Counter, writes: ["value"] });

export const count = command({
  emits: [counted],
}).decide(({ records }) => [emit(counted, { value: records.Counter.value + 1 })]);

export const counter = machine({
  description: "Count on every count, going back and forth between two states",
  receives: { counted },
  commands: { count },
  initial: "ping",
  states: { ping: {}, pong: {} },
}).chart({
  states: {
    ping: { on: { counted: [{ target: "pong" }] }, sends: { count: { onAccepted: [], onRejected: [] } } },
    pong: { on: { counted: [{ target: "ping" }] }, sends: { count: { onAccepted: [], onRejected: [] } } },
  },
});
